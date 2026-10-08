-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_norm_sq_le_pow_gs
-- name    : LLLFactor.RedBasis.norm_sq_le_pow_gs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:24.194984+00:00
-- url     : https://prove2.me/theorems/9a3104cf-dd51-4e41-b411-38e496b5457b
-- title:
--   Proof of (1.6), p. 517 — |b_i|² = |b_i*|² + Σ μ_ij²|b_j*|² ≤ 2^{i−1}·|b_i*|²
-- statement:
--   Let $b_1,\ldots,b_n$ be a linearly independent, reduced family in $\mathbb R^n$ ($n\ge1$) with Gram–Schmidt vectors $b_i^*$ and coefficients $\mu_{ij}$. For $1\le i\le n$,
--
--   $$|b_i|^2=|b_i^*|^2+\sum_{j=1}^{i-1}\mu_{ij}^2|b_j^*|^2\qquad\text{and}\qquad |b_i|^2\le 2^{i-1}\,|b_i^*|^2 .$$
--
--   The identity follows from (1.2) and the orthogonality of the $b_j^*$; the inequality uses (1.4) and the comparison $|b_j^*|^2\le 2^{i-j}|b_i^*|^2$. In the proof of Proposition (1.6) this bound is the link between the lengths of the basis vectors and those of their orthogonalisations.
--
--   **Formalization Note** Both the identity and the final inequality of the page's chain are stated, as a conjunction; the intermediate lines are steps of the computation. Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index. At Lean index $0$ the bound reads $|b_1|^2\le 2^0|b_1^*|^2$, at index $1$ it reads $|b_2|^2\le 2^1|b_2^*|^2$, as on the page. The sum over $j<i$ is over `Finset.Iio i`.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 517, proof of (1.6); DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem norm_sq_le_pow_gs {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (hred : IsReduced b) :
  ∀ i : Fin n,
    ‖b i‖ ^ 2 = ‖gs b i‖ ^ 2 + ∑ j ∈ Finset.Iio i, mu b i j ^ 2 * ‖gs b j‖ ^ 2 ∧
      ‖b i‖ ^ 2 ≤ (2 : ℝ) ^ (i : ℕ) * ‖gs b i‖ ^ 2 := by sorry
end LLLFactor.RedBasis
