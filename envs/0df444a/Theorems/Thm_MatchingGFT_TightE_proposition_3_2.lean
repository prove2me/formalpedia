-- Prove2me | Theorems.Thm_MatchingGFT_TightE_proposition_3_2
-- name    : MatchingGFT.TightE.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:58.629808+00:00
-- url     : https://prove2.me/theorems/2bd0755d-34e2-4524-9fd1-4881a94c9bdc
-- title:
--   Proposition 3.2 — Edge-selection regions
-- statement:
--   For every edge $e=(i,j)$ and external rank profile, $\mathcal D_e^{\omega_{-e}}$ is a measurable down-set on which $Q_i(\rho)\ge Q_j(\sigma)$ almost everywhere; and $\mathrm{FB}=\sum_e E_{\omega_{-e}}\int_{\mathcal D_e^{\omega_{-e}}}(Q_i(\rho)-Q_j(\sigma))\,d\rho\,d\sigma$.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - encoding: the external ranks ω₋ₑ of all agents other than i, j → a full rank vector whose entries i, j are overwritten; the expectation is over all ranks; reason: the integrand does not depend on those two entries
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Proposition 3.2, PDF p. 12

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_Regions

open MeasureTheory Set

namespace MatchingGFT.TightE

/-- Proposition 3.2 (PDF p. 12): for every edge `e = (i, j)` and every external rank profile, (i) the
selection region is a measurable down-set and (ii) `Qᵢ(ρ) ≥ Qⱼ(σ)` almost everywhere on it; and (iii) `FB`
is the sum over edges of the expected integrals of `Qᵢ(ρ) - Qⱼ(σ)` over the regions. -/
theorem proposition_3_2 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) :
    (∀ e ∈ m.edges, ∀ ω : Profile B S, (∀ i, ω.1 i ∈ Ioo (0 : ℝ) 1) → (∀ j, ω.2 j ∈ Ioo (0 : ℝ) 1) →
      IsRankDownSet (edgeRegion m rank e ω) ∧
      ∀ᵐ p ∂(volume.restrict (edgeRegion m rank e ω)),
        sellerQuantile (m.sellerLaw e.2) p.2 ≤ buyerQuantile (m.buyerLaw e.1) p.1) ∧
    firstBestValue m rank =
      ∑ e ∈ m.edges, ∫ ω, (∫ p in edgeRegion m rank e ω,
        (buyerQuantile (m.buyerLaw e.1) p.1 - sellerQuantile (m.sellerLaw e.2) p.2)) ∂rankMeasure B S := by sorry

end MatchingGFT.TightE
