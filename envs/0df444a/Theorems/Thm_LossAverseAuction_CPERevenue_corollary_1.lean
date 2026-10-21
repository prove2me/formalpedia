-- Prove2me | Theorems.Thm_LossAverseAuction_CPERevenue_corollary_1
-- name    : LossAverseAuction.CPERevenue.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:31.871236+00:00
-- url     : https://prove2.me/theorems/de7afaf6-d839-4c41-a6f2-ed72d900b86d
-- title:
--   Corollary 1, p. 11 — FPA revenue exceeds SPA revenue with monetary loss aversion
-- statement:
--   Let $\beta_I$ and $\beta_{II}$ be symmetric increasing FPA and SPA CPE strategies, and let $R_I,R_{II}$ be the expected total payments from all $N\ge2$ bidders. Then
--
--   $$\Lambda^m=0\Longrightarrow R_{II}=R_I,\qquad \Lambda^m>0\Longrightarrow R_{II}<R_I.$$
--
--   This is the paper’s seller-revenue ranking under choice-acclimating personal equilibrium.
--
--   **Formalization Note** Revenue is the expectation of actual payments under the product signal law. Assumption 1 is maintained from p. 5.
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §4.3, Corollary 1, p. 11 (PDF 12)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

namespace LossAverseAuction.CPERevenue

open MeasureTheory

theorem corollary_1 {m : ℕ} (E : Env m) (hS : E.Standing)
    (hA1 : E.Assumption1) (βI βII : ℝ → ℝ)
    (hI : E.IsSymCPE .FPA βI) (hII : E.IsSymCPE .SPA βII) :
    (E.Lm = 0 → E.revenue .SPA βII = E.revenue .FPA βI) ∧
    (0 < E.Lm → E.revenue .SPA βII < E.revenue .FPA βI) := by sorry
end LossAverseAuction.CPERevenue
