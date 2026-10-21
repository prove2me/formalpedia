-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_kelly_zero_not_eq
-- name    : LiquidPoA.Kelly.kelly_zero_not_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:05.213252+00:00
-- url     : https://prove2.me/theorems/e3ee7414-715a-487a-8635-d2758d469b02
-- title:
--   Section 2, p. 5 — a valuable positive-budget player rules out zero equilibrium
-- statement:
--   If an admissible Kelly game has a player $i$ with positive budget $c_i$ and $v_i(1)>v_i(0)$, the all-zero signal vector is not an equilibrium:
--
--   $$
--   c_i>0,\quad v_i(1)>v_i(0)\quad\Longrightarrow\quad 0\notin eq(G^{Kelly}).
--   $$
--
--   A sufficiently small positive signal obtains the resource at a payment below both the budget and the player's gain in value. This identifies when the zero profile can matter in the full price-of-anarchy goal.
--
--   **Formalization Note** The value condition makes precise the paper's phrase “valuation function that takes positive values”; a positive constant valuation alone would not give a profitable deviation.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, p. 5, paragraph preceding the definition of X_n

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Section 2, pp. 5–6: a player with positive budget and genuinely increasing value rules out zero equilibrium. -/
theorem kelly_zero_not_eq {n : ℕ} (G : RAGame n)
    (hG : G.IsAdmissible) (i : Fin n)
    (hc : 0 < G.c i) (hv : G.v i 0 < G.v i 1) :
    ¬ IsEquilibrium (kelly n) G 0 := by sorry

end LiquidPoA.Kelly
