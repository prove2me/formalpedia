-- Prove2me | Theorems.Thm_MatchingGFT_TightE_proposition_3_6
-- name    : MatchingGFT.TightE.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:11.670196+00:00
-- url     : https://prove2.me/theorems/cf009506-803a-4a45-b79d-e5ea030255a3
-- title:
--   Proposition 3.6 — Realizing the section benchmarks
-- statement:
--   $\sum_{e}E_{\omega_{-e}}[P_S(\mathcal D_e^{\omega_{-e}})]\le\mathrm{OPT}^S$ and $\sum_{e}E_{\omega_{-e}}[P_B(\mathcal D_e^{\omega_{-e}})]\le\mathrm{OPT}^B$, with $P_S,P_B$ taken at the quantiles of the edge's endpoints and OPT the true suprema.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - encoding: a possibly randomized one-sided auction with realized payments → a lottery over the family with expected payments; reason: BIC, interim IR and the objective use expectations only
--   - encoding: interim and ex-ante expectations of payments → families are required to have integrable payments; reason: an expectation that is undefined has no meaning in the source; the requirement excludes only such families
--   - encoding: the external ranks ω₋ₑ → a full rank vector whose entries i, j are overwritten; reason: the integrand does not depend on those entries
--   - encoding: inequality of real quantities → inequality in EReal against the extended-real supremum; reason: OPT is an extended-real supremum
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Proposition 3.6, PDF p. 14

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile
import Definitions.Def_MatchingGFT_TightE_OneSided
import Definitions.Def_MatchingGFT_TightE_Regions

open MeasureTheory

namespace MatchingGFT.TightE

/-- Proposition 3.6 (PDF p. 14): `Σ_e E_{ω₋ₑ}[P_S(𝒟_e^{ω₋ₑ})] ≤ OPT^S` and `Σ_e E_{ω₋ₑ}[P_B(𝒟_e^{ω₋ₑ})] ≤ OPT^B`. -/
theorem proposition_3_6 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) :
    ((∑ e ∈ m.edges, ∫ ω, benchmarkS (buyerQuantile (m.buyerLaw e.1))
        (sellerQuantile (m.sellerLaw e.2)) (edgeRegion m rank e ω) ∂rankMeasure B S : ℝ) : EReal) ≤
      optS m ∧
    ((∑ e ∈ m.edges, ∫ ω, benchmarkB (buyerQuantile (m.buyerLaw e.1))
        (sellerQuantile (m.sellerLaw e.2)) (edgeRegion m rank e ω) ∂rankMeasure B S : ℝ) : EReal) ≤
      optB m := by sorry

end MatchingGFT.TightE
