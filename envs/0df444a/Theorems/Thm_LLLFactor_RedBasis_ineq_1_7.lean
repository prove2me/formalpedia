-- Prove2me | Theorems.Thm_LLLFactor_RedBasis_ineq_1_7
-- name    : LLLFactor.RedBasis.ineq_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:19:28.571987+00:00
-- url     : https://prove2.me/theorems/764455d0-616e-4dc3-851a-6e1465c53796
-- title:
--   (1.7): reduced-basis vector bound
-- statement:
--   Let $b_1,\ldots,b_n$ be a reduced basis for a lattice $L$ in $\mathbb R^n$ ($n\ge1$), and let $b_1^*,\ldots,b_n^*$ be its Gram–Schmidt vectors. Then
--
--   $$|b_j|^2\le 2^{i-1}\,|b_i^*|^2\qquad\text{for }1\le j\le i\le n .$$
--
--   This is inequality (1.7) of Proposition (1.6). It bounds every earlier basis vector by a later Gram–Schmidt length and is the estimate used in the proofs of (1.11) and (1.12).
--
--   **Formalization Note** Lean indexes the basis by $\{0,\ldots,n-1\}$, so the paper's $b_i$ is Lean's `b ⟨i-1, _⟩`; a paper exponent $2^{i-1}$ at index $i$ becomes `2 ^ (i : ℕ)` at the Lean index.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 517, (1.6) Proposition, (1.7); DOI: https://doi.org/10.1007/BF01457454

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting

namespace LLLFactor.RedBasis

theorem ineq_1_7 {n : ℕ} (hn : 0 < n) (L : Submodule ℤ (Vec n))
  (b : Fin n → Vec n) (hb : IsBasisFor b L) (hred : IsReduced b) :
  ∀ i j : Fin n, j ≤ i → ‖b j‖ ^ 2 ≤ (2 : ℝ) ^ (i : ℕ) * ‖gs b i‖ ^ 2 := by sorry
end LLLFactor.RedBasis
