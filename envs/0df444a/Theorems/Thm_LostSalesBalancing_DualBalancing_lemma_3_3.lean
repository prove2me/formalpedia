-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_lemma_3_3
-- name    : LostSalesBalancing.DualBalancing.lemma_3_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:28.13687+00:00
-- url     : https://prove2.me/theorems/9d2825e9-c268-4806-8a22-ad53b6ea5432
-- title:
--   Lemma 3.3 — global lost-sales penalty comparison
-- statement:
--   Run two nonnegative order sequences $B$ and $P$ against the same nonnegative demand path and initial pipeline. Let $\mathcal T_\Pi$ be the order periods $t\in[1,T-L]$ for which at least one truncated position $Y^B_{st}$, $s\in[t,t+L]$, is at least $Y^P_{st}$. If $\Pi_t^Q=p_{t+L}(d_{t+L}-I_{t+L}^Q)^+$, then
--
--   $$
--   \sum_{t\in\mathcal T_\Pi}\Pi_t^B\le\sum_{t=1}^{T-L}\Pi_t^P.
--   $$
--
--   This global comparison bounds the marked lost-sales charges of $B$ by the comparison policy's charges across the horizon.
--
--   **Formalization Note** The paper names the comparison policy OPT. Here it is any nonnegative order sequence. The lost-sales penalty rates are nonnegative and non-increasing, as in the extension after the lemma on p. 14. The instance also contains ordering-cost monotonicity, which this lemma does not use. The sum on the right covers penalty periods $L+1,\ldots,T$.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript pp. 11–14, §3.2, Lemma 3.3 and remark

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset
open scoped Classical

/-- Lemma 3.3: global amortization of marked lost-sales penalties. -/
theorem lemma_3_3 (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j) :
    (∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter (fun t => ¬ InTH I d QB QP t),
      lostLS I d QB t) ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), lostLS I d QP t := by sorry

end LostSalesBalancing.DualBalancing
