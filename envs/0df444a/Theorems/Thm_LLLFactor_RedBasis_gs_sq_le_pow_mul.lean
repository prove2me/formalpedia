-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_gs_sq_le_pow_mul
-- name    : LLLFactor.RedBasis.gs_sq_le_pow_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:11.437582+00:00
-- url     : https://prove2.me/theorems/e09b5bb5-5f07-4181-ab86-0e8deeac6275
-- title:
--   Proof of (1.6): Gram–Schmidt length comparison
-- statement:
--   Let $b_1,\ldots,b_n$ be a linearly independent, reduced family in $\mathbb R^n$ ($n\ge1$) with Gram–Schmidt vectors $b_i^*$. Then
--
--   $$|b_j^*|^2\le 2^{i-j}\,|b_i^*|^2\qquad\text{for }1\le j\le i\le n .$$
--
--   This is the induction step of the proof of Proposition (1.6): iterating the consecutive bound $|b_i^*|^2\ge\frac12|b_{i-1}^*|^2$ compares any two Gram–Schmidt lengths.
--
--   **Formalization Note** Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index. The exponent $i-j$ is a difference of indices and is unchanged by the shift; it is a natural-number subtraction, nontruncated because $j\le i$. Only linear independence of the $b_i$ is assumed, not a lattice.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 517, proof of (1.6); DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem gs_sq_le_pow_mul {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (hred : IsReduced b) :
  ∀ i j : Fin n, j ≤ i → ‖gs b j‖ ^ 2 ≤
    (2 : ℝ) ^ ((i : ℕ) - (j : ℕ)) * ‖gs b i‖ ^ 2 := by sorry
end LLLFactor.RedBasis
