-- Prove2me | Theorems.Thm_MatchingGFT_TightE_lemma_B_3
-- name    : MatchingGFT.TightE.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:54.549075+00:00
-- url     : https://prove2.me/theorems/3e1997b7-5209-4fc4-8fa6-b408462b2b75
-- title:
--   Lemma B.3 — Atoms are not split
-- statement:
--   Fix all reports except one endpoint of $e$. Two ranks with the same reported type both select $e$ in the first-best matching or neither does; consequently a nonempty initial selection interval does not end in the interior of the quantile interval of an atom. Stated for each endpoint.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - encoding: a nonempty selection interval; the interior of an atom interval → selection length ℓ > 0; ℓ outside the open interval (P[v > a], P[v ≥ a]) (seller: (P[c < a], P[c ≤ a])) of an atom a; reason: Appendix A gives these endpoints; a nonempty subset of (0,1) has positive supremum
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Lemma B.3, PDF pp. 25–26

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regions

open Set

namespace MatchingGFT.TightE

/-- Lemma B.3 (PDF pp. 25–26), for each endpoint of `e`: two ranks with the same reported type either both
select `e` in the first-best matching or neither does; consequently a nonempty initial selection
interval does not end in the interior of the quantile interval of an atom. -/
theorem lemma_B_3 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) (e : B × S) (he : e ∈ m.edges) (t : Profile B S)
    (ht : IsNonnegProfile t) :
    (∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ ρ' ∈ Ioo (0 : ℝ) 1,
      buyerQuantile (m.buyerLaw e.1) ρ = buyerQuantile (m.buyerLaw e.1) ρ' →
      (e ∈ firstBest m rank (updateBuyer t e.1 (buyerQuantile (m.buyerLaw e.1) ρ)) ↔
        e ∈ firstBest m rank (updateBuyer t e.1 (buyerQuantile (m.buyerLaw e.1) ρ')))) ∧
    (∀ a : ℝ, 0 < (m.buyerLaw e.1).real {a} → 0 < edgeSectionLengthBuyer m rank e t →
      edgeSectionLengthBuyer m rank e t ∉
        Ioo ((m.buyerLaw e.1).real (Ioi a)) ((m.buyerLaw e.1).real (Ici a))) ∧
    (∀ σ ∈ Ioo (0 : ℝ) 1, ∀ σ' ∈ Ioo (0 : ℝ) 1,
      sellerQuantile (m.sellerLaw e.2) σ = sellerQuantile (m.sellerLaw e.2) σ' →
      (e ∈ firstBest m rank (updateSeller t e.2 (sellerQuantile (m.sellerLaw e.2) σ)) ↔
        e ∈ firstBest m rank (updateSeller t e.2 (sellerQuantile (m.sellerLaw e.2) σ')))) ∧
    (∀ a : ℝ, 0 < (m.sellerLaw e.2).real {a} → 0 < edgeSectionLengthSeller m rank e t →
      edgeSectionLengthSeller m rank e t ∉
        Ioo ((m.sellerLaw e.2).real (Iio a)) ((m.sellerLaw e.2).real (Iic a))) := by sorry

end MatchingGFT.TightE
