-- Prove2me | Theorems.Thm_MinBuying_mtp2_integrable_marginal
-- name    : MinBuying.mtp2_integrable_marginal
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:53:24.66534+00:00
-- url     : https://prove2.me/theorems/0046200c-ed34-47f3-8f9a-59ef67812e69
-- title:
--   Integrating an MTP2 density over integrable one-coordinate fibers preserves MTP2
-- statement:
--   Let $f:\mathbb R^{n+1}\to\mathbb R$ be nonnegative and pointwise MTP2, and let $\nu$ be any measure on the first real coordinate. If every one-coordinate fiber $t\mapsto f(t,v)$ is integrable with respect to $\nu$, then $v\mapsto\int f(t,v)\,d\nu(t)$ is pointwise MTP2. Neither continuity nor strict positivity is assumed.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary measure-theoretic closure step for the proof of Theorem 2, ec3. The explicit every-fiber integrability assumption is part of this helper, not an extra hypothesis on the paper theorem.

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinBuying

theorem mtp2_integrable_marginal (n : ℕ) (f : Valuations (n+1) → ℝ)
    (hf : ∀ v, 0 ≤ f v) (hmtp : MTP2 f) (μ : Measure ℝ)
    (hi : ∀ v : Valuations n, Integrable (fun t : ℝ => f (Fin.cons t v)) μ) :
    MTP2 (fun v : Valuations n => ∫ t : ℝ, f (Fin.cons t v) ∂μ) := by
  sorry

end MinBuying
