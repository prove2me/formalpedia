-- Prove2me | Theorems.Thm_LossAverseAuction_CPERevenue_proposition_11
-- name    : LossAverseAuction.CPERevenue.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:37.452979+00:00
-- url     : https://prove2.me/theorems/8479fcf6-2e89-45c2-bd28-a6bf2cecdc98
-- title:
--   Proposition 11, p. 11 — equal utility and FPA payment dominance
-- statement:
--   For symmetric FPA and SPA CPE strategies, equilibrium utility is equal for every supported type. Let $P_I$ and $P_{II}$ be their expected payments. Then
--
--   $$EU_I(t,t)=EU_{II}(t,t),\quad \Lambda^m>0\Longrightarrow P_{II}(t)<P_I(t)\ (t>\underline t),\quad \Lambda^m=0\Longrightarrow P_{II}(t)=P_I(t).$$
--
--   This is the bidder-level comparison behind the revenue corollary.
--
--   **Formalization Note** The zero-loss-aversion payment equality comes from the proof; the printed proposition states the strict positive-loss-aversion inequality.
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §4.3, Proposition 11, p. 11 (PDF 12); proof p. 17 (PDF 18)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

namespace LossAverseAuction.CPERevenue

open MeasureTheory

theorem proposition_11 {m : ℕ} (E : Env m) (hS : E.Standing)
    (hA1 : E.Assumption1) (βI βII : ℝ → ℝ)
    (hI : E.IsSymCPE .FPA βI) (hII : E.IsSymCPE .SPA βII) :
    (∀ t ∈ Set.Icc E.tl E.th, E.eqUtil .FPA βI t = E.eqUtil .SPA βII t) ∧
    (0 < E.Lm → ∀ t ∈ Set.Ioc E.tl E.th,
      E.interimPayment .SPA βII t < E.interimPayment .FPA βI t) ∧
    (E.Lm = 0 → ∀ t ∈ Set.Icc E.tl E.th,
      E.interimPayment .SPA βII t = E.interimPayment .FPA βI t) := by sorry
end LossAverseAuction.CPERevenue
