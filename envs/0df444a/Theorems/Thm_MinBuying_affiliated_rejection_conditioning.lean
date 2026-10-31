-- Prove2me | Theorems.Thm_MinBuying_affiliated_rejection_conditioning
-- name    : MinBuying.affiliated_rejection_conditioning
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T17:15:46.947697+00:00
-- url     : https://prove2.me/theorems/3f089a55-f308-45a4-b527-cf51cb0fac92
-- title:
--   Affiliation and exchangeability after rejection conditioning
-- statement:
--   Let $(V_0,V_1,\ldots,V_n)$ have an exchangeable affiliated probability law supported on nonnegative valuations. Affiliation is the paper's density-or-PMF MTP2 condition. For a real threshold $a$, suppose $\Pr(V_0<a)>0$. Then the conditional law of the remaining vector
--
--   $$(V_1,\ldots,V_n)\mid\{V_0<a\}$$
--
--   is again a nonnegative probability law, exchangeable, and affiliated. This is the closure step that lets the induction for optimal uniform pricing continue after the cheapest item has been rejected.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, electronic companion ec3, proof of Theorem 2, closure under conditioning on an interval and marginalization; Definition 1 for affiliation.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

/-- Closure step in the proof of Theorem 2, ec3: condition on rejection of the
first item and retain the remaining coordinates. -/
theorem affiliated_rejection_conditioning (n : ℕ) (μ : JointLaw (n+1))
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (a : ℝ) (hB : 0 < μ {v : Valuations (n+1) | v 0 < a}) :
    let ν : JointLaw n := Measure.map (fun v : Valuations (n+1) => fun i : Fin n => v i.succ)
      (ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a})
    ValidLaw ν ∧ Exchangeable ν ∧ Affiliated ν := by
  sorry

end MinBuying
