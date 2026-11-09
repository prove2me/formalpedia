-- Prove2me | Theorems.Thm_MatchingGFT_TightE_lemma_B_1
-- name    : MatchingGFT.TightE.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:07.437201+00:00
-- url     : https://prove2.me/theorems/4c93dfa8-bc13-4589-a022-620d8d2a9c60
-- title:
--   Lemma B.1 — Measurable section lengths
-- statement:
--   For an edge $e$, the buyer-quantile selection length $\ell_{B,e}$ is a measurable function of the fixed reports, and so is the seller-quantile length $\ell_{S,e}$.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - generalization: measurable in the fixed (nonnegative) reports → measurable on all real profiles, the updated entry being overwritten; reason: restricting to nonnegative reports gives the source claim
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Lemma B.1, PDF p. 25

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Regions

namespace MatchingGFT.TightE

/-- Lemma B.1 (PDF p. 25): for an edge `e`, the buyer-quantile selection length `ℓ_{B,e}` is a measurable
function of the fixed reports, and so is the seller-quantile length `ℓ_{S,e}`. -/
theorem lemma_B_1 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) (e : B × S) (he : e ∈ m.edges) :
    Measurable (edgeSectionLengthBuyer m rank e) ∧ Measurable (edgeSectionLengthSeller m rank e) := by sorry

end MatchingGFT.TightE
