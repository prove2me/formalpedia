-- Prove2me | Theorems.Thm_MinBuying_density_rejection_representation
-- name    : MinBuying.density_rejection_representation
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:06:29.40968+00:00
-- url     : https://prove2.me/theorems/1f65596a-5778-4e1f-8ac4-d52b5cf41e00
-- title:
--   Rejection conditioning has a normalized integrable MTP2 density
-- statement:
--   Let a probability law on $n+1$ real coordinates have a measurable nonnegative pointwise-MTP2 density $f$. Conditional on any positive-probability event $V_0<a$, it has an integrable measurable nonnegative pointwise-MTP2 density $g$. The conditional measure equals Lebesgue measure weighted by $g$ exactly; no positivity or continuity assumption on $f$ is imposed.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary affiliation and conditioning steps for the proof of Theorem 2, ec2–ec3. For association, the finite four-functions theorem is reused from Mathlib/Combinatorics/SetFamily/FourFunctions.lean.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinBuying

theorem density_rejection_representation (n : ℕ) (μ : JointLaw (n+1)) (hμ : IsProbabilityMeasure μ)
    (f : Valuations (n+1) → ℝ) (hm : Measurable f) (hf : ∀ v,0 ≤ f v) (hmtp : MTP2 f)
    (hden : μ = volume.withDensity (fun v => ENNReal.ofReal (f v))) (a : ℝ)
    (hB : 0 < μ {v : Valuations (n+1) | v 0 < a}) :
    ∃ g : Valuations (n+1) → ℝ, Measurable g ∧ (∀ v,0 ≤ g v) ∧ MTP2 g ∧
      Integrable g volume ∧
      ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a} =
        volume.withDensity (fun v => ENNReal.ofReal (g v)) := by
  sorry

end MinBuying
