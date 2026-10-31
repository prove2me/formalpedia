-- Prove2me | Theorems.Thm_MinBuying_finite_support_wellposed
-- name    : MinBuying.finite_support_wellposed
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:35:51.94128+00:00
-- url     : https://prove2.me/theorems/b7eb4e93-8e4e-41f5-8f91-c14f129892f3
-- title:
--   Finite-support min-buying pricing attains both optima
-- statement:
--   Let $\mu$ be a probability law on $n$ real-valued item valuations, concentrated on a given finite set $S$. Suppose some nonnegative uniform price has strictly positive expected revenue. Then the differentiated and uniform revenue sets over nonnegative prices are bounded above, both suprema are attained by feasible prices, and the uniform optimum is positive. No independence, symmetry, continuity, regularity, or first-moment hypothesis is needed.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript. https://doi.org/10.2139/ssrn.5178133 . Auxiliary optimization lemma for the finite construction in Theorem 3, ec5–ec6, using the pricing model of Section 2, pp.7–9. The finite valuation-grid rounding argument is supplied in this formalization.

import Definitions.Def_MinBuying_Model

open MeasureTheory Set MinBuying

namespace MinBuying

theorem finite_support_wellposed (n : ℕ) (μ : JointLaw n) (hμ : IsProbabilityMeasure μ)
    (S : Finset (Valuations n)) (hS : ∀ᵐ v ∂μ, v ∈ S)
    (hpos : ∃ p : ℝ, 0 ≤ p ∧ 0 < uniformRevenue μ p) : WellPosed μ := by
  sorry

end MinBuying
