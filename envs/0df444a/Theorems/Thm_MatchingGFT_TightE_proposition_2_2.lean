-- Prove2me | Theorems.Thm_MatchingGFT_TightE_proposition_2_2
-- name    : MatchingGFT.TightE.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:40.906798+00:00
-- url     : https://prove2.me/theorems/87afe78a-0a7e-4e4d-bf79-5ff3bef58a87
-- title:
--   Proposition 2.2 — GFT dominates one-sided profit
-- statement:
--   For every seller-side auction family that is interim IR for the buyers, $E[\mathrm{GFT}]\ge E[\pi^S]$; for every buyer-side one interim IR for the sellers, $E[\mathrm{GFT}]\ge E[\pi^B]$. BIC is not assumed.
--
--   Differences from the source:
--   - encoding: a possibly randomized one-sided auction with realized payments → a lottery over the family with expected payments; reason: BIC, interim IR and the objective use expectations only
--   - encoding: interim and ex-ante expectations of payments → families are required to have integrable payments; reason: an expectation that is undefined has no meaning in the source; the requirement excludes only such families
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Proposition 2.2, PDF p. 11

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_OneSided

open MeasureTheory

namespace MatchingGFT.TightE

/-- Proposition 2.2 (PDF p. 11): every seller-side auction family that is interim IR for the buyers has
`E[GFT] ≥ E[π^S]`, and every buyer-side one that is interim IR for the sellers has `E[GFT] ≥ E[π^B]`. -/
theorem proposition_2_2 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) :
    (∀ a : AuctionFamily B S B, IsBuyerAuctionFamily m a → IsInterimIRBuyers m a →
      ∫ t, objectiveS m a t ∂typeMeasure m ≤ ∫ t, lotteryGFT m a t ∂typeMeasure m) ∧
    (∀ a : AuctionFamily B S S, IsSellerAuctionFamily m a → IsInterimIRSellers m a →
      ∫ t, objectiveB m a t ∂typeMeasure m ≤ ∫ t, lotteryGFT m a t ∂typeMeasure m) := by sorry

end MatchingGFT.TightE
