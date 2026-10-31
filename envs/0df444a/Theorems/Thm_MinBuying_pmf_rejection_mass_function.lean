-- Prove2me | Theorems.Thm_MinBuying_pmf_rejection_mass_function
-- name    : MinBuying.pmf_rejection_mass_function
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:05:33.351982+00:00
-- url     : https://prove2.me/theorems/c7108eb2-c738-4d14-90b0-f89b69d637b6
-- title:
--   Explicit MTP2 PMF witness after rejection conditioning and projection
-- statement:
--   For an MTP2 probability mass function $w$ on $n+1$ real-valued coordinates, condition on a positive-probability rejection event $V_0<a$ and retain the remaining coordinates. There exists a probability mass function $z$ on those coordinates whose associated measure equals this conditional projected law, and whose real-valued masses are pointwise MTP2. The statement supplies the PMF witness explicitly for a discrete-law induction and allows countably infinite support.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary affiliation and conditioning steps for the proof of Theorem 2, ec2–ec3. For association, the finite four-functions theorem is reused from Mathlib/Combinatorics/SetFamily/FourFunctions.lean.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

theorem pmf_rejection_mass_function (n : ℕ) (w : PMF (Valuations (n+1)))
    (hmtp : MTP2 (fun v => (w v).toReal)) (a : ℝ)
    (hB : 0 < w.toMeasure {v : Valuations (n+1) | v 0 < a}) :
    ∃ z : PMF (Valuations n),
      Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
        (ProbabilityTheory.cond w.toMeasure {v : Valuations (n+1) | v 0 < a}) = z.toMeasure ∧
      MTP2 (fun v => (z v).toReal) := by
  sorry

end MinBuying
