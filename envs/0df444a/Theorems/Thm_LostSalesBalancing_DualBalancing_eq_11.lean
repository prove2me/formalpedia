-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_eq_11
-- name    : LostSalesBalancing.DualBalancing.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:01.614913+00:00
-- url     : https://prove2.me/theorems/c47f55c0-6aa3-45b2-8f7e-8d22930cefb0
-- title:
--   (11) — on-hand inventory from truncated position and lost demand
-- statement:
--   Fix a nonnegative demand path and a nonnegative order sequence in the finite-horizon lost-sales model. For $1\le t\le s\le t+L\le T$, let $Y_{st}$ be the inventory on hand in period $s$ plus orders outstanding in $s$ that were placed no later than $t$. Then
--
--   $$
--   I_{t+L}=Y_{st}-\sum_{r=s}^{t+L-1}d_r+\sum_{r=s}^{t+L-1}(d_r-I_r)^+.
--   $$
--
--   This identity relates a truncated inventory position to subsequent on-hand stock and accounts exactly for demand lost between $s$ and $t+L$.
--
--   **Formalization Note** The paper's (11) writes the final sum as cumulative lost-sales penalties divided by a stationary positive $p$. We state lost units directly, which also covers time-dependent or zero penalty rates without division by zero. Periods are integers; empty endpoint sums have value zero.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript p. 13, §3.2, (11)

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset LeviBalancing.DualBalancing

/-- Equation (11), expressed in lost units so it remains valid for varying or zero penalties. -/
theorem eq_11 (I : LSInstance) (d Q : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hQ : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ Q j)
    (t s : ℤ) (ht : 1 ≤ t) (hs : t ≤ s) (hst : s ≤ t + I.L)
    (hT : t + I.L ≤ (I.T : ℤ)) :
    onHand I d Q (t + I.L) =
      truncPos I d Q s t - cumDemand d s (t + I.L - 1) +
        ∑ r ∈ Icc s (t + I.L - 1), lostUnits I d Q r := by sorry

end LostSalesBalancing.DualBalancing
