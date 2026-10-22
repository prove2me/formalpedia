-- Prove2me | Theorems.Thm_LiquidPoA_Kelly_kelly_not_eq_one_positive
-- name    : LiquidPoA.Kelly.kelly_not_eq_one_positive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:17.870661+00:00
-- url     : https://prove2.me/theorems/7322338b-0fa7-4082-bc0e-c3280c3d6a76
-- title:
--   Section 2, pp. 5–6 — a sole positive Kelly signal is not an equilibrium
-- statement:
--   In an admissible Kelly game, a signal vector with exactly one positive entry is not a pure Nash equilibrium:
--
--   $$
--   s_i>0,\quad s_j=0\ (j\ne i)\quad\Longrightarrow\quad s\notin eq(G^{Kelly}).
--   $$
--
--   The sole positive player can lower her payment while retaining the entire resource. This removes the nonzero signal profiles outside $\mathbb X_n$ from the full price-of-anarchy goal.
-- source:
--   Caragiannis, Voudouris, The efficiency of resource allocation mechanisms for budget-constrained users, arXiv:1707.03551v3, pp. 5–6, paragraph preceding the definition of X_n

import Mathlib
import Definitions.Def_LiquidPoA_Kelly_Setting

namespace LiquidPoA.Kelly

/-- Section 2, pp. 5–6: a sole positive Kelly signal cannot be an equilibrium. -/
theorem kelly_not_eq_one_positive {n : ℕ} (G : RAGame n)
    (hG : G.IsAdmissible) (s : Fin n → ℝ) (hs : IsSignal s)
    (i : Fin n) (hi : 0 < s i)
    (hothers : ∀ j, j ≠ i → s j = 0) :
    ¬ IsEquilibrium (kelly n) G s := by sorry

end LiquidPoA.Kelly
