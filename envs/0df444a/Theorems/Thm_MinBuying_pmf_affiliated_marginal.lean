-- Prove2me | Theorems.Thm_MinBuying_pmf_affiliated_marginal
-- name    : MinBuying.pmf_affiliated_marginal
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:53:22.455557+00:00
-- url     : https://prove2.me/theorems/bfb11971-9234-4044-a177-ba1f571fa424
-- title:
--   An MTP2 probability mass function retains MTP2 after dropping one coordinate
-- statement:
--   For a probability mass function on $n+1$ real-valued coordinates whose real-valued masses are pointwise MTP2, the probability mass function obtained by retaining the last $n$ coordinates is also pointwise MTP2. This includes arbitrary countably supported laws on real valuation vectors.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary marginalization step for the proof of Theorem 2, ec3, under the density-or-PMF affiliation definition on pp.12–13.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

theorem pmf_affiliated_marginal (n : ℕ) (w : PMF (Valuations (n+1)))
    (hmtp : MTP2 (fun v => (w v).toReal)) :
    MTP2 (fun v : Valuations n =>
      ((w.map (fun y : Valuations (n+1) => fun i : Fin n => y i.succ)) v).toReal) := by
  sorry

end MinBuying
