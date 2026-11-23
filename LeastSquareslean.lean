/-
Copyright (c) 2026 Xiaokang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiaokang Yu
-/
module

public import Mathlib

/-!
# Optimality and uniqueness of least-squares solutions

Starting from a given solution of the normal equations, we prove
residual orthogonality, a loss decomposition, global optimality,
a characterisation of all minimisers, and uniqueness under
linear independence of the columns.
We also prove nonuniqueness when a nonzero kernel direction is given.
Existence of a normal-equation solution is outside the scope.
-/

@[expose] public section

namespace LeastSquares

/-! ## Squared Euclidean length -/

/-- The squared Euclidean length of a finite real vector. -/
noncomputable def sqNorm {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  dotProduct v v

/-- Squared Euclidean length is the sum of coordinate squares. -/
lemma sqNorm_eq_sum {m : ℕ} (v : Fin m → ℝ) :
    sqNorm v = ∑ i, (v i) ^ 2 := by
  simp only [sqNorm, dotProduct, pow_two]

/-- Squared Euclidean length is nonnegative. -/
lemma sqNorm_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ sqNorm v := by
  rw [sqNorm_eq_sum]
  apply Finset.sum_nonneg
  intro i _hi
  exact sq_nonneg (v i)

/-- Only the zero vector has zero squared Euclidean length. -/
lemma sqNorm_eq_zero_iff {m : ℕ} (v : Fin m → ℝ) :
    sqNorm v = 0 ↔ v = 0 := by
  exact dotProduct_self_eq_zero

/-- Expansion of the squared length of a difference. -/
lemma sqNorm_sub {m : ℕ} (u v : Fin m → ℝ) :
    sqNorm (u - v) = sqNorm u + sqNorm v - 2 * dotProduct u v := by
  unfold sqNorm
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm v u]
  ring

/-! ## Definitions -/

variable {n p : ℕ}
variable (x : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)

/-- The residual sum of squares associated with a parameter vector. -/
noncomputable def loss (β : Fin p → ℝ) : ℝ :=
  sqNorm (y - x.mulVec β)

/-- A global minimiser has loss no greater than that at any other parameter. -/
def IsMinimiser (β₀ : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, loss x y β₀ ≤ loss x y β

/-- A parameter satisfies the normal equations. -/
def NormalEquations (βhat : Fin p → ℝ) : Prop :=
  x.transpose.mulVec (x.mulVec βhat) = x.transpose.mulVec y

/-! ## Basic properties -/

/-- A solution of the normal equations satisfies the defining equality. -/
lemma NormalEquations.eq {β : Fin p → ℝ} (h : NormalEquations x y β) :
    x.transpose.mulVec (x.mulVec β) = x.transpose.mulVec y := by
  exact h

/-- Equal fitted vectors give equal losses. -/
lemma loss_eq_of_fit_eq {β γ : Fin p → ℝ}
    (h : x.mulVec β = x.mulVec γ) : loss x y β = loss x y γ := by
  unfold loss
  rw [h]

/-- The transpose of x annihilates the residual of a normal-equation solution. -/
lemma NormalEquations.transpose_mulVec_residual_eq_zero {β : Fin p → ℝ}
    (h : NormalEquations x y β) :
    x.transpose.mulVec (y - x.mulVec β) = 0 := by
  rw [Matrix.mulVec_sub, ← h.eq, sub_self]

/-! ## Assumptions for the main results -/

variable {βhat : Fin p → ℝ}
variable (hNormal : NormalEquations x y βhat)

/-! ## Lemma 1: residual orthogonality -/

include hNormal in
/-- The residual is orthogonal to every vector of the form xd. -/
lemma residual_orthogonality (d : Fin p → ℝ) :
    dotProduct (y - x.mulVec βhat) (x.mulVec d) = 0 := by
  calc
    dotProduct (y - x.mulVec βhat) (x.mulVec d)
        = dotProduct d (x.transpose.mulVec (y - x.mulVec βhat)) := by
            exact (Matrix.dotProduct_transpose_mulVec x d (y - x.mulVec βhat)).symm
    _ = 0 := by rw [hNormal.transpose_mulVec_residual_eq_zero, dotProduct_zero]

/-! ## Lemma 2: decomposition of the residual sum of squares -/

include hNormal in
/-- The loss splits into the reference loss and a squared length. -/
lemma loss_decomposition (β : Fin p → ℝ) :
    loss x y β = loss x y βhat + sqNorm (x.mulVec (β - βhat)) := by
  have hResidual :
      y - x.mulVec β = (y - x.mulVec βhat) - x.mulVec (β - βhat) := by
    rw [Matrix.mulVec_sub]
    abel
  unfold loss
  rw [hResidual, sqNorm_sub]
  rw [residual_orthogonality x y hNormal (β - βhat)]
  ring

/-! ## Theorem 1: optimality -/

include hNormal in
/-- Every solution of the normal equations is a global minimiser. -/
theorem normalEquations_isMinimiser : IsMinimiser x y βhat := by
  intro β
  rw [loss_decomposition x y hNormal β]
  exact le_add_of_nonneg_right (sqNorm_nonneg (x.mulVec (β - βhat)))

/-! ## Theorem 2: characterisation of all minimisers -/

include hNormal in
/-- Minimisers are exactly the parameters with the reference fitted vector. -/
theorem isMinimiser_iff_fit_eq (β : Fin p → ℝ) :
    IsMinimiser x y β ↔ x.mulVec β = x.mulVec βhat := by
  constructor
  · intro hMin
    have hLoss : loss x y β = loss x y βhat :=
      le_antisymm (hMin βhat) (normalEquations_isMinimiser x y hNormal β)
    have hSquare : sqNorm (x.mulVec (β - βhat)) = 0 := by
      have hDecomposition := loss_decomposition x y hNormal β
      linarith
    have hZero : x.mulVec (β - βhat) = 0 :=
      (sqNorm_eq_zero_iff (x.mulVec (β - βhat))).mp hSquare
    rw [Matrix.mulVec_sub] at hZero
    exact sub_eq_zero.mp hZero
  · intro h z
    rw [loss_eq_of_fit_eq x y h]
    exact normalEquations_isMinimiser x y hNormal z

/-! ## Corollary: uniqueness under full column rank -/

include hNormal in
/-- Linearly independent columns give a unique global minimiser. -/
theorem existsUnique_minimiser_of_fullColumnRank :
    LinearIndependent ℝ x.col → ∃! β : Fin p → ℝ, IsMinimiser x y β := by
  intro h1
  use βhat
  constructor
  · exact normalEquations_isMinimiser x y hNormal
  · intro β hismin
    have hequal : x.mulVec β = x.mulVec βhat := by
      exact (isMinimiser_iff_fit_eq x y hNormal β).mp hismin
    have hInjective : Function.Injective x.mulVec := by
      exact Matrix.mulVec_injective_iff.mpr h1
    exact hInjective hequal

/-! ## Further discussion: nonuniqueness along a nonzero kernel direction -/

include hNormal in
/-- A nonzero kernel direction gives a minimiser distinct from βhat. -/
theorem exists_minimiser_ne_of_nonzero_kernel
    (d : Fin p → ℝ) (hd : x.mulVec d = 0) (hne : d ≠ 0) :
    ∃ β : Fin p → ℝ, IsMinimiser x y β ∧ β ≠ βhat := by
  use βhat + d
  constructor
  · have hFit : x.mulVec (βhat + d) = x.mulVec βhat := by
      rw [Matrix.mulVec_add, hd, add_zero]
    exact (isMinimiser_iff_fit_eq x y hNormal (βhat + d)).mpr hFit
  · intro hEq
    apply hne
    calc
      d = (βhat + d) - βhat := by abel
      _ = 0 := by rw [hEq, sub_self]

include hNormal in
/-- A nonzero kernel direction prevents uniqueness of the global minimiser. -/
theorem not_existsUnique_minimiser_of_nonzero_kernel
    (d : Fin p → ℝ) (hd : x.mulVec d = 0) (hne : d ≠ 0) :
    ¬ (∃! β : Fin p → ℝ, IsMinimiser x y β) := by
  obtain ⟨β, hMin, hNe⟩ :=
    exists_minimiser_ne_of_nonzero_kernel x y hNormal d hd hne
  intro hUnique
  obtain ⟨γ, _hγ, hUniqueness⟩ := hUnique
  have hEq : β = βhat := by
    calc
      β = γ := hUniqueness β hMin
      _ = βhat := (hUniqueness βhat
        (normalEquations_isMinimiser x y hNormal)).symm
  exact hNe hEq

end LeastSquares
