-- Prove2me | Theorems.Thm_MinBuying_pmf_rejection_conditioning
-- name    : MinBuying.pmf_rejection_conditioning
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:05:26.684242+00:00
-- url     : https://prove2.me/theorems/a9423d60-3875-41ad-8f56-8e4a231381ca
-- title:
--   Rejection conditioning and projection preserve PMF affiliation
-- statement:
--   Let $w$ be a probability mass function on $n+1$ real-valued coordinates with pointwise-MTP2 real masses. If the rejection event $V_0<a$ has positive probability, then conditioning on this event and retaining the last $n$ coordinates gives an affiliated law. The law is represented by a PMF, with no finite-support assumption.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary affiliation and conditioning steps for the proof of Theorem 2, ec2–ec3. For association, the finite four-functions theorem is reused from Mathlib/Combinatorics/SetFamily/FourFunctions.lean.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

theorem pmf_rejection_conditioning (n : ℕ) (w : PMF (Valuations (n+1)))
    (hmtp : MTP2 (fun v => (w v).toReal)) (a : ℝ)
    (hB : 0 < w.toMeasure {v : Valuations (n+1) | v 0 < a}) :
    Affiliated (Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
      (ProbabilityTheory.cond w.toMeasure {v : Valuations (n+1) | v 0 < a})) := by
  sorry

end MinBuying
