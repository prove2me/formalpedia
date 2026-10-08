-- Prove2me | Theorems.Thm_OnlineStochMatching_SuggestedMatching_cut_identity
-- name    : OnlineStochMatching.SuggestedMatching.cut_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:31.26998+00:00
-- url     : https://prove2.me/theorems/527aecaf-a2fa-428e-95a9-7b8d05ac382e
-- title:
--   §4.1 Bounding OPT — canonical cut identity
-- statement:
--   For any maximum integral expected-instance matching $M$, let $A_S,I_S$ be the advertiser and type vertices reachable from the source in its residual network, and let $A_T=A\setminus A_S$. No edge of the original graph joins $A_S$ to a type outside $I_S$, and
--
--   $$|A^*|=|A_T|+\sum_{i\in I_S}e_i.$$
--
--   The identity equates the size of the selected integral flow with the capacity of its canonical minimum cut. It supports the scenario-wise bound on hindsight optimum.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 5, §4.1, Bounding OPT, cut identity

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- Section 4.1's canonical cut has no advertiser-to-type crossing edge,
and its capacity equals the maximum integral flow. -/
theorem cut_identity (A I : Type) [Fintype A] [Fintype I]
    (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) :
    (∀ a i, (a, i) ∈ inst.E → adInSourceSide inst M a → typeInSourceSide inst M i) ∧
      (coveredAds M).card =
        (adsInSinkSide inst M).card +
          ∑ i ∈ typesInSourceSide inst M, inst.e i := by sorry

end OnlineStochMatching.SuggestedMatching
