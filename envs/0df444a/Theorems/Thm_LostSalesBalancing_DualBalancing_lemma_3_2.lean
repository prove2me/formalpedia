-- Prove2me | Theorems.Thm_LostSalesBalancing_DualBalancing_lemma_3_2
-- name    : LostSalesBalancing.DualBalancing.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:42:11.605909+00:00
-- url     : https://prove2.me/theorems/04d9f3bc-1843-4a99-b913-c229c3604f38
-- title:
--   Lemma 3.2 — holding costs on the all-strictly-lower periods
-- statement:
--   Run two nonnegative order sequences $B$ and $P$ against one nonnegative demand path and the same initial pipeline. Let $\mathcal T_H$ contain those order periods $t\in[1,T-L]$ for which every truncated position $Y^B_{st}$, $s\in[t,t+L]$, is strictly below $Y^P_{st}$. If $H_t^Q$ is the marginal holding cost of order $t$ plus its ordering cost under policy $Q$, then
--
--   $$
--   \sum_{t\in\mathcal T_H}H_t^B\le\sum_{t=1}^{T-L}H_t^P.
--   $$
--
--   The inequality charges the marked holding costs of one path to the comparison path and forms one side of the pathwise cost comparison.
--
--   **Formalization Note** The paper calls $P$ the optimum and writes its overall holding cost on the right; the statement uses any comparison order sequence and its marginal holding total. Ordering costs are included in $H_t$ as allowed after (5), under non-increasing nonnegative rates. The instance also contains non-increasing lost-sales rates, although this lemma does not use them.
-- source:
--   Levi, Janakiraman, Nagarajan, A 2-Approximation Algorithm for Stochastic Inventory Control Models with Lost Sales, Math. Oper. Res. 33(2) (2008), accepted manuscript p. 11, §3.2, Lemma 3.2 and following remark

import Mathlib
import Definitions.Def_LostSalesBalancing_DualBalancing_Model

namespace LostSalesBalancing.DualBalancing

open Finset
open scoped Classical

/-- Lemma 3.2: marginal holding and ordering costs from the marked periods are paid by
the comparison policy's marginal holding and ordering costs. -/
theorem lemma_3_2 (I : LSInstance) (d QB QP : ℤ → ℝ)
    (hd : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ d j)
    (hB : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QB j)
    (hP : ∀ j : ℤ, 1 ≤ j → j ≤ (I.T : ℤ) → 0 ≤ QP j) :
    (∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter (fun t => InTH I d QB QP t),
      holdingLS I d QB t) ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), holdingLS I d QP t := by sorry

end LostSalesBalancing.DualBalancing
