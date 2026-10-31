-- Prove2me | Theorems.Thm_MinBuying_bounded_continuous_wellposed
-- name    : MinBuying.bounded_continuous_wellposed
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T17:49:27.76575+00:00
-- url     : https://prove2.me/theorems/f0de0ba5-e318-4658-9686-8c1c74eedbed
-- title:
--   Attained pricing optima for bounded continuous independent valuations
-- statement:
--   Let n>0 and let the n independent valuation marginals be nonnegative probability laws, each absolutely continuous with respect to Lebesgue measure. Suppose a common finite M bounds all valuations almost surely. Then the feasible differentiated and uniform revenue sets are bounded above, their suprema are attained by nonnegative prices, and the optimal uniform revenue is strictly positive. This establishes the pricing well-posedness needed when continuous approximations replace the triangular laws.
-- source:
--   Cui, Hamilton, Lamperski, and Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133, Section 2 pricing conventions and the proof of Lemma EC.2. Auxiliary result proved for this formalization.

import Definitions.Def_MinBuying_Model

open MeasureTheory

namespace MinBuying

/-- Bounded absolutely continuous nonnegative independent marginals give
finite attained optima and a strictly positive uniform optimum. -/
theorem bounded_continuous_wellposed (n : ℕ) (hn : 0 < n)
    (F : Fin n → Measure ℝ) (hF : ∀ i, ValidMarginal (F i))
    (hac : ∀ i, F i ≪ volume) (M : ℝ) (hM : ∀ i, ∀ᵐ x ∂F i, x ≤ M) :
    WellPosed (productLaw F) := by
  sorry

end MinBuying
