-- Prove2me | Theorems.Thm_MatchingGFT_TightE_corollary_3_3
-- name    : MatchingGFT.TightE.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:50.922204+00:00
-- url     : https://prove2.me/theorems/de81fda6-0074-48b1-982a-f073cd184e48
-- title:
--   Corollary 3.3 — Stable partner
-- statement:
--   With all other reports fixed, all first-best matchings in which a buyer is matched, as her report varies, use the same seller; symmetrically for every seller.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Corollary 3.3, PDF p. 13

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

namespace MatchingGFT.TightE

/-- Corollary 3.3 (PDF p. 13): with all other reports fixed, all first-best matchings in which buyer
`i` is matched, over her reports, use the same seller; symmetrically for every seller. -/
theorem corollary_3_3 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) :
    (∀ t : Profile B S, IsNonnegProfile t → ∀ (i : B) (x x' : ℝ) (j j' : S), 0 ≤ x → 0 ≤ x' →
      (i, j) ∈ firstBest m rank (updateBuyer t i x) →
      (i, j') ∈ firstBest m rank (updateBuyer t i x') → j = j') ∧
    (∀ t : Profile B S, IsNonnegProfile t → ∀ (j : S) (x x' : ℝ) (i i' : B), 0 ≤ x → 0 ≤ x' →
      (i, j) ∈ firstBest m rank (updateSeller t j x) →
      (i', j) ∈ firstBest m rank (updateSeller t j x') → i = i') := by sorry

end MatchingGFT.TightE
