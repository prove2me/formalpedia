-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_kelly_sup_ratio
-- name    : LiquidPoA.Kelly.kelly_sup_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:10.996003+00:00
-- url     : https://prove2.me/theorems/0cd89307-c396-490b-aa98-f48f034dc393
-- title:
--   Proof of Theorem 5.1, p. 15 — the supremum is 2
-- statement:
--   For at least two Kelly players, the supremum of the ratio in equation (6) over signal vectors with at least two positive coordinates is
--
--   $$
--   \sup_{s\in\mathbb X_n}
--   \frac{\sum_{i\ge2}p_i^{Kelly}(s)+\lambda_1^{Kelly}(s)}{\sum_{i\ge2}p_i^{Kelly}(s)+\lambda_1^{Kelly}(s)g_1^{Kelly}(s)}=2.
--   $$
--
--   The value is a supremum: for two players it is approached as the first signal tends to zero while remaining positive. It supplies the numerical bound for Theorem 5.1.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 15, proof of Theorem 5.1, last line of displayed calculation

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- The final supremum in the display on p. 15 is exactly two. -/
theorem kelly_sup_ratio (n : ℕ) (hn : 2 ≤ n) :
    (⨆ (s : Fin n → ℝ) (_ : InX s),
      ratio (kelly n) s (⟨0, by omega⟩ : Fin n)) = 2 := by sorry

end LiquidPoA.Kelly
