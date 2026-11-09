-- Prove2me | Theorems.Thm_KSPolySign_lemma_3_7_b
-- name    : KSPolySign.lemma_3_7_b
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:38:21.507185+00:00
-- url     : https://prove2.me/theorems/a0dd652e-0960-457b-aed3-5a3c754fdeb6
-- title:
--   Lemma 3.7(b) — the linearized constraint map is invertible and order-preserving
-- statement:
--   Let $(b,U,V)$ be the optimizer at $y\in[-1,1]^k$. On pairs of Hermitian matrices define
--   $$\mathcal J(X,Y) = \big(U^{-1}XU^{-1}-K_y(Y),\ V^{-1}YV^{-1}-K_y(X)\big).$$
--   Then $\mathcal J$ is self-adjoint for $\langle(A,B),(C,D)\rangle=\mathrm{tr}[AC]+\mathrm{tr}[BD]$, it is invertible, and its inverse preserves the positive semidefinite order (componentwise on pairs). The dual multipliers $(W,Z)$ of part (a) are unique.
--
--   **Formalization Note** Invertibility: every Hermitian pair has exactly one Hermitian preimage. Order preservation: if $\mathcal J(X',Y')-\mathcal J(X,Y)$ is componentwise positive semidefinite, so is $(X'-X,Y'-Y)$. Uniqueness of the multipliers: two pairs of positive definite matrices satisfying (7) coincide.
--
--   Differences from the source:
--   - generalization: the normalized inputs Ā_i of Lemma 3.1 (F = 0) → every maintained instance: PSD rank-one C_i with ∑C_i² ⪯ I, any Hermitian F, any ρ > 0; reason: Definition 3.5 evaluates this notation with C_i in place of Ā_i, and the normalized inputs are such an instance (ζ ≤ 1); the statement specializes to the source's
--   - encoding: matrices in ℂ^{n×n} with nonzero inputs (so n ≥ 1) → explicit hypothesis 1 ≤ n; reason: excludes only 0×0 matrices, where the program of Definition 3.3 is degenerate and P has no meaning
--   - encoding: J on Hermitian pairs, invertible, inverse preserves PSD order → unique Hermitian preimage of every Hermitian pair; J(X′,Y′) − J(X,Y) ⪰ 0 componentwise implies (X′,Y′) − (X,Y) ⪰ 0; reason: these are the definitions of the printed properties
--   - encoding: the optimizer (b, U, V) → any optimizer; reason: the optimizer is unique (Lemma 3.7(a)); same instances
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(b), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_KSPolySign_IsOptimal
import Definitions.Def_KSPolySign_IsInstance
import Definitions.Def_KSPolySign_IsDualPair
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 3.7(b) (The linearized constraint map).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(b), p.19 (PDF p.19).

At the optimizer `(b, U, V)` of `y ∈ [−1, 1]^k`, the map on Hermitian pairs
`J(X, Y) = (U⁻¹XU⁻¹ − K_y(Y), V⁻¹YV⁻¹ − K_y(X))` is self-adjoint for
`⟨(A, B), (C, D)⟩ = tr[AC] + tr[BD]`, invertible, and its inverse preserves positive semidefinite
order. The dual multipliers `(W, Z)` are unique.

**Formalization Note** Stated for every maintained instance (Definition 3.5: nonzero PSD rank-one `C_i` with `∑ C_i² ⪯ I`, a fixed Hermitian `F`) and every `ρ > 0`; the normalized inputs are the case `F = 0`, `C_i = Ā_i`. `n ≥ 1` excludes `0 × 0` matrices. Invertibility on Hermitian pairs: every Hermitian pair has
exactly one Hermitian preimage. "The inverse preserves semidefinite order": if `J(X', Y') − J(X, Y)` is
componentwise PSD, so is `(X', Y') − (X, Y)`. Uniqueness of the dual multipliers: any two pairs of
positive definite matrices satisfying Eq. (7) coincide. -/
theorem lemma_3_7_b (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (y : Fin k → ℝ) (hy : ∀ i, |y i| ≤ 1) (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ) (hopt : IsOptimal C F ρ y b U V) :
    let J : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ := fun X Y =>
      (U⁻¹ * X * U⁻¹ - coupling C y Y, V⁻¹ * Y * V⁻¹ - coupling C y X)
    (∀ X Y X' Y' : Matrix (Fin n) (Fin n) ℂ, X.IsHermitian → Y.IsHermitian → X'.IsHermitian → Y'.IsHermitian →
        ((J X Y).1 * X').trace + ((J X Y).2 * Y').trace =
          (X * (J X' Y').1).trace + (Y * (J X' Y').2).trace) ∧
      (∀ A B : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian → B.IsHermitian →
        ∃! XY : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ, XY.1.IsHermitian ∧ XY.2.IsHermitian ∧ J XY.1 XY.2 = (A, B)) ∧
      (∀ X Y X' Y' : Matrix (Fin n) (Fin n) ℂ, X.IsHermitian → Y.IsHermitian → X'.IsHermitian → Y'.IsHermitian →
        ((J X' Y').1 - (J X Y).1).PosSemidef → ((J X' Y').2 - (J X Y).2).PosSemidef →
        (X' - X).PosSemidef ∧ (Y' - Y).PosSemidef) ∧
      ∀ W Z W' Z' : Matrix (Fin n) (Fin n) ℂ, IsDualPair C ρ y U V W Z → IsDualPair C ρ y U V W' Z' →
        W = W' ∧ Z = Z' := by sorry

end KSPolySign
