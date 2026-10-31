-- Prove2me | Theorems.Thm_MinBuying_rejection_valid_exchangeable
-- name    : MinBuying.rejection_valid_exchangeable
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:53:25.572548+00:00
-- url     : https://prove2.me/theorems/e3c69cf7-1555-4051-b615-9986dcd78a84
-- title:
--   Rejection conditioning preserves validity and exchangeability of the remaining valuations
-- statement:
--   For any nonnegative exchangeable probability law on $n+1$ item valuations, conditioning on the positive-probability event $V_0<a$ and then retaining coordinates $1,\ldots,n$ produces a nonnegative exchangeable probability law. This result does not require affiliation.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Proof of Theorem 2, ec3: conditioning on rejection of the first item and retaining the remaining coordinates.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinBuying

theorem rejection_valid_exchangeable (n : ℕ) (μ : JointLaw (n+1)) (hμ : ValidLaw μ)
    (hex : Exchangeable μ) (a : ℝ)
    (hB : 0 < μ {v : Valuations (n+1) | v 0 < a}) :
    let ν : JointLaw n := Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
      (ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a})
    ValidLaw ν ∧ Exchangeable ν := by
  sorry

end MinBuying
