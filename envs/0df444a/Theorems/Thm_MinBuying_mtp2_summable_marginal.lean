-- Prove2me | Theorems.Thm_MinBuying_mtp2_summable_marginal
-- name    : MinBuying.mtp2_summable_marginal
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:53:27.424055+00:00
-- url     : https://prove2.me/theorems/5f65db41-470a-4ae6-872d-7c494155dea0
-- title:
--   Summing an MTP2 mass function over one coordinate preserves MTP2
-- statement:
--   Let $f:\mathbb R^{n+1}\to\mathbb R$ be nonnegative and pointwise MTP2. If every first-coordinate fiber $t\mapsto f(t,v)$ is summable, then the marginal $v\mapsto\sum_t f(t,v)$ is pointwise MTP2. The sum may have countably infinite support; no finite-support assumption is imposed.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary marginalization step for the proof of Theorem 2, ec3, under the density-or-PMF affiliation definition on pp.12–13.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory

namespace MinBuying

theorem mtp2_summable_marginal (n : ℕ) (f : Valuations (n+1) → ℝ)
    (hf : ∀ v, 0 ≤ f v) (hmtp : MTP2 f)
    (hs : ∀ v : Valuations n, Summable (fun t : ℝ => f (Fin.cons t v))) :
    MTP2 (fun v : Valuations n => ∑' t : ℝ, f (Fin.cons t v)) := by
  sorry

end MinBuying
