-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_gs_sq_ge_half_prev
-- name    : LLLFactor.RedBasis.gs_sq_ge_half_prev
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:02.727988+00:00
-- url     : https://prove2.me/theorems/5fd459aa-03a0-4665-a262-ff97e4dae573
-- title:
--   Proof of (1.6), p. 517 — |b_i*|² ≥ (¾ − μ²_{i i−1})·|b*_{i−1}|² ≥ ½·|b*_{i−1}|²
-- statement:
--   Let $b_1,\ldots,b_n$ be a linearly independent family in $\mathbb R^n$ ($n\ge1$) that is reduced in the sense of (1.4)–(1.5), with Gram–Schmidt vectors $b_i^*$ and coefficients $\mu_{ij}$. Then for $1<i\le n$
--
--   $$|b_i^*|^2\ \ge\ \bigl(\tfrac34-\mu_{i\,i-1}^2\bigr)\,|b_{i-1}^*|^2\ \ge\ \tfrac12\,|b_{i-1}^*|^2 .$$
--
--   The first inequality comes from (1.5), the second from (1.4). This is the step in the proof of Proposition (1.6) that the induction to (1.7) is built on: consecutive Gram–Schmidt lengths cannot shrink by more than a factor $\sqrt2$.
--
--   **Formalization Note** Both inequalities of the chain are stated, as a conjunction. Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index. The lattice $L$ itself plays no role, so only linear independence of the $b_i$ is assumed.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 517, proof of (1.6); DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem gs_sq_ge_half_prev {n : ℕ} (hn : 0 < n) (b : Fin n → Vec n)
  (hb : LinearIndependent ℝ b) (hred : IsReduced b) :
  ∀ (i : ℕ) (hi : i + 1 < n),
    ((3 / 4 : ℝ) - mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤
        ‖gs b ⟨i + 1, hi⟩‖ ^ 2 ∧
      (1 / 2 : ℝ) * ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤
        ((3 / 4 : ℝ) - mu b ⟨i + 1, hi⟩ ⟨i, by omega⟩ ^ 2) * ‖gs b ⟨i, by omega⟩‖ ^ 2 := by sorry
end LLLFactor.RedBasis
