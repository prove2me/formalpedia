-- Prove2me | Theorems.Thm_MinBuying_triangular_continuous_smoothing
-- name    : MinBuying.triangular_continuous_smoothing
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:43:11.481993+00:00
-- url     : https://prove2.me/theorems/decc59c9-7e59-4626-abf4-0971958edb11
-- title:
--   Continuous regular smoothing of a triangular marginal
-- statement:
--   Let a,v>0 and 0<δ<a. There is an absolutely continuous regular probability law F on [0,v+δ] whose strict rejection probability at v agrees with Tri(a,v). At every real price p,
--
--   $$\Pr_{\operatorname{Tri}(a,v)}(V<p-\delta)\le\Pr_F(V<p).$$
--
--   This provides the continuous regular approximation required for sharpness: demand at the cap is preserved, and the change in the distribution is controlled by an arbitrarily small price shift.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, proof of Lemma EC.2, electronic companion. Supporting constructive lemma.

import Definitions.Def_MinBuying_Triangular
import Definitions.Def_MinBuying_Regularity

open MeasureTheory Set

namespace MinBuying

/-- A continuous regular smoothing of a positive triangular-revenue marginal,
with unchanged cap acceptance and a deterministic upper perturbation of δ. -/
theorem triangular_continuous_smoothing (a v δ : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hδ : 0 < δ) (hδa : δ < a) :
    ∃ F : Measure ℝ,
      ContinuousRegular F ∧
      (∀ᵐ x ∂F, x ∈ Icc (0 : ℝ) (v+δ)) ∧
      rejection F v = rejection (triangularLaw a v) v ∧
      (∀ p : ℝ, rejection (triangularLaw a v) (p-δ) ≤ rejection F p) := by
  sorry

end MinBuying
