-- Prove2me | Theorems.Thm_KSPolySign_lemma_3_7_a
-- name    : KSPolySign.lemma_3_7_a
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:53.791199+00:00
-- url     : https://prove2.me/theorems/9bdfabf1-eefa-4ba2-b5cc-80f567c7402b
-- title:
--   Lemma 3.7(a) — unique optimizer and optimality equations
-- statement:
--   Fix $y\in[-1,1]^k$ and put $M=M(y)$. The program defining $P(y)$ has a unique optimizer $(b,U,V)$, and there are positive definite dual multipliers $(W,Z)$ with
--   $$\mathrm{tr}[W+Z]=1,\qquad W=UK_y(Z)U+\rho U^2,\qquad Z=VK_y(W)V+\rho V^2,\tag{7}$$
--   $$U^{-1}+M+K_y(V)=bI,\qquad V^{-1}-M+K_y(U)=bI.\tag{8}$$
--
--   Both matrix constraints are tight at the optimum; these equations are the basis of every derivative computation for $P$.
--
--   Differences from the source:
--   - generalization: the normalized inputs Ā_i of Lemma 3.1 (F = 0) → every maintained instance: PSD rank-one C_i with ∑C_i² ⪯ I, any Hermitian F, any ρ > 0; reason: Definition 3.5 evaluates this notation with C_i in place of Ā_i, and the normalized inputs are such an instance (ζ ≤ 1); the statement specializes to the source's
--   - encoding: matrices in ℂ^{n×n} with nonzero inputs (so n ≥ 1) → explicit hypothesis 1 ≤ n; reason: excludes only 0×0 matrices, where the program of Definition 3.3 is degenerate and P has no meaning
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(a), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_KSPolySign_IsOptimal
import Definitions.Def_KSPolySign_IsInstance
import Definitions.Def_KSPolySign_IsDualPair
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 3.7(a) (Optimizer and optimality equations).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(a), p.19 (PDF p.19).

Fix `y ∈ [−1, 1]^k`. The program of Definition 3.3 has a unique optimizer `(b, U, V)` and positive
definite dual multipliers `(W, Z)` satisfying Eq. (7), `tr[W + Z] = 1`, `W = UK_y(Z)U + ρU²`,
`Z = VK_y(W)V + ρV²`, and Eq. (8), `U⁻¹ + M + K_y(V) = bI`, `V⁻¹ − M + K_y(U) = bI`.

**Formalization Note** Stated for every maintained instance (Definition 3.5: nonzero PSD rank-one `C_i` with `∑ C_i² ⪯ I`, a fixed Hermitian `F`) and every `ρ > 0`; the normalized inputs are the case `F = 0`, `C_i = Ā_i`. `n ≥ 1` excludes `0 × 0` matrices. -/
theorem lemma_3_7_a (n k : ℕ) (hn : 1 ≤ n) (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (hC : IsInstance C)
    (F : Matrix (Fin n) (Fin n) ℂ) (hF : F.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (y : Fin k → ℝ) (hy : ∀ i, |y i| ≤ 1) :
    ∃ (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ), IsOptimal C F ρ y b U V ∧
      (∀ (b' : ℝ) (U' V' : Matrix (Fin n) (Fin n) ℂ), IsOptimal C F ρ y b' U' V' → b' = b ∧ U' = U ∧ V' = V) ∧
      ∃ W Z : Matrix (Fin n) (Fin n) ℂ, IsDualPair C ρ y U V W Z ∧
        U⁻¹ + Msum C F y + coupling C y V = ((b : ℝ) : ℂ) • 1 ∧
        V⁻¹ - Msum C F y + coupling C y U = ((b : ℝ) : ℂ) • 1 := by sorry

end KSPolySign
