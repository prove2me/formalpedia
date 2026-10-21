-- Prove2me | Theorems.Thm_LossAverseAuction_CPERevenue_equation_10
-- name    : LossAverseAuction.CPERevenue.equation_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:26.955606+00:00
-- url     : https://prove2.me/theorems/d166cee2-dfc2-47e3-a1a0-acf197684c04
-- title:
--   Eq. (10), p. 10 — FPA direct utility under CPE
-- statement:
--   For a symmetric FPA CPE strategy, a type-$t$ bidder bids as type $\widetilde t>t$. Write $V$ for expected value conditional on winning, $\Psi$ and $\Omega$ for the extensive and intensive item-risk terms, and $\mathcal T_I$ for the FPA payment term. Then
--
--   $$EU_I(\widetilde t,t)=F_1(\widetilde t)V(\widetilde t,t)-\Psi(\widetilde t,t)-\Omega(\widetilde t,t)-\mathcal T_I(\widetilde t).$$
--
--   This relates primitive lottery utility to the FPA reduced form.
--
--   **Formalization Note** The intensive-risk expectation has the deviation-lottery weight F1(tilde t) squared; the page prints an inconsistent F1(t) F1(tilde t).
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §4.1, eq. (10), p. 10 (PDF 11)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

namespace LossAverseAuction.CPERevenue

open MeasureTheory

theorem equation_10 {m : ℕ} (E : Env m) (hS : E.Standing) (hA1 : E.Assumption1)
    (β : ℝ → ℝ) (hβ : E.IsSymCPE .FPA β) (t t' : ℝ)
    (ht : t ∈ Set.Icc E.tl E.th) (ht' : t' ∈ Set.Icc E.tl E.th)
    (hdev : t < t') :
    E.EU (E.Γ .FPA β (β t') t) (E.Γ .FPA β (β t') t) =
      E.F1 t' * E.Vc t' t - E.Psi t' t - E.Omega t' t - E.TI β t' := by sorry
end LossAverseAuction.CPERevenue
