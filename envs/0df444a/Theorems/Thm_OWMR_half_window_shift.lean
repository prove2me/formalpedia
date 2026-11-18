-- Prove2me | Theorems.Thm_OWMR_half_window_shift
-- name    : OWMR.half_window_shift
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:40.8022+00:00
-- url     : https://prove2.me/theorems/bb5d310d-40e4-482d-992f-0154bb0046e3
-- title:
--   Half-window shift: $\max_{0\le\upsilon\le b}\int_{[0,b)}g(\upsilon+x)\,U(dx)\ge\frac12\int_{[0,2b)}g\,dU$
-- statement:
--   Let $U$ be the renewal measure of i.i.d. nonnegative demands with positive mean. Let $b>0$ and let $g$ be continuous, nonnegative, and concave on $[0,2b]$. Then some shift $\upsilon\in[0,b]$ satisfies
--
--   $$\int_{[0,2b)}g(x)\,U(dx)\le 2\int_{[0,b)}g(\upsilon+x)\,U(dx).$$
--
--   Equivalently, the best shifted half window retains at least half of the full-window savings, which is (16).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 5 (Half-Window Shift), eq. (16), p. 16; proof on pp. 16-17.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem half_window_shift (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (b : ℝ) (hb : 0 < b) (g : ℝ → ℝ)
    (hgc : ContinuousOn g (Set.Icc 0 (2 * b))) (hg0 : ∀ x ∈ Set.Icc 0 (2 * b), 0 ≤ g x)
    (hgconc : ConcaveOn ℝ (Set.Icc 0 (2 * b)) g) :
    ∃ υ ∈ Set.Icc 0 b, ∫ x in Set.Ico 0 (2 * b), g x ∂(renewalMeasure ρ)
      ≤ 2 * ∫ x in Set.Ico 0 b, g (υ + x) ∂(renewalMeasure ρ) := by sorry
end OWMR
