-- Prove2me | Theorems.Thm_LossAverseAuction_CPERevenue_equation_12
-- name    : LossAverseAuction.CPERevenue.equation_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:34.621797+00:00
-- url     : https://prove2.me/theorems/02bf861c-0a78-4d22-8f07-f6d9b3ca746c
-- title:
--   Eq. (12), p. 11 — SPA direct utility under CPE
-- statement:
--   For a symmetric SPA CPE strategy, a type-$t$ bidder bids as type $\widetilde t>t$. With the same $F_1,V,\Psi,\Omega$ and the SPA payment term $\mathcal T_{II}$,
--
--   $$EU_{II}(\widetilde t,t)=F_1(\widetilde t)V(\widetilde t,t)-\Psi(\widetilde t,t)-\Omega(\widetilde t,t)-\mathcal T_{II}(\widetilde t).$$
--
--   The item-risk terms coincide across formats and the monetary term differs.
--
--   **Formalization Note** The intensive-risk expectation uses the deviation lottery and needs no conditional-value density. The paper’s printed prefactor is corrected as in equation (10).
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §4.2, eq. (12), p. 11 (PDF 12)

import Mathlib
import Definitions.Def_LossAverseAuction_CPERevenue_Model

namespace LossAverseAuction.CPERevenue

open MeasureTheory

theorem equation_12 {m : ℕ} (E : Env m) (hS : E.Standing) (hA1 : E.Assumption1)
    (β : ℝ → ℝ) (hβ : E.IsSymCPE .SPA β) (t t' : ℝ)
    (ht : t ∈ Set.Icc E.tl E.th) (ht' : t' ∈ Set.Icc E.tl E.th)
    (hdev : t < t') :
    E.EU (E.Γ .SPA β (β t') t) (E.Γ .SPA β (β t') t) =
      E.F1 t' * E.Vc t' t - E.Psi t' t - E.Omega t' t - E.TII β t' := by sorry
end LossAverseAuction.CPERevenue
