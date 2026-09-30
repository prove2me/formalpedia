-- Prove2me | Theorems.Thm_InfoSharing_Diseconomy_prop_1b_no_free_sharing
-- name    : InfoSharing.Diseconomy.prop_1b_no_free_sharing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T06:18:30.939728+00:00
-- url     : https://prove2.me/theorems/70cafdec-1058-49e9-b617-178f4b864d48
-- title:
--   Proposition 1(b) — without contracting the retailer shares no information
-- statement:
--   Under the hypotheses of Lemma 3, suppose the retailer chooses the information statuses freely, with no side payment. Then a retailer-optimal status profile exists, and every retailer-optimal profile has
--
--   $$n = 0.$$
--
--   This is the benchmark that motivates the paid contracting of §5.2.
--
--   **Formalization Note.** The pricing stage is the Bayesian game of §4.1 on the signal model; the ex ante profits $M$, $R$ are those of an arbitrary pricing-equilibrium family, not the §4.2 closed forms. Wholesale strategies are measurable, square-integrable functions of the signal value (constants for an uninformed manufacturer); the production cost is $bq + cq^2$ with $c = c_d > 0$ and $b > 0$; manufacturers are indexed by $\{0,1\}$.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 253, Proposition 1(b)

import Mathlib
import Definitions.Def_InfoSharing_Shared_IsSignalModel
import Definitions.Def_InfoSharing_Shared_PayoffTable
open MeasureTheory
open InfoSharing.Shared

namespace InfoSharing.Diseconomy

/-- Proposition 1(b), p. 253: without information contracting, the retailer does not share any
information — a retailer-optimal status profile exists, and every one has no informed
manufacturer. -/
theorem prop_1b_no_free_sharing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (θ Y : Ω → ℝ) (a b c φ σ β : ℝ) (hmodel : IsSignalModel μ θ Y σ β) (hφ : 0 < φ)
    (hb : 0 < b) (hc : 0 < c) (E : (Fin 2 → Status) → PricingProfile)
    (hE : IsPricingEqFamily μ θ Y a b c φ β E) :
    let P := payoffTable μ θ Y a b c φ E
    (∃ X : Fin 2 → Status, IsNoContractOutcome P X) ∧
    ∀ X : Fin 2 → Status, IsNoContractOutcome P X → numInformed X = 0 := by sorry

end InfoSharing.Diseconomy
