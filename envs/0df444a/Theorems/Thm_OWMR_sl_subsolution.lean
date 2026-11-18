-- Prove2me | Theorems.Thm_OWMR_sl_subsolution
-- name    : OWMR.sl_subsolution
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T04:27:02.91798+00:00
-- url     : https://prove2.me/theorems/6eebbc30-66ad-4e3a-804d-196f00fece0c
-- title:
--   Single-location value and bounded relative value: $J=\mathcal J_D(f;K)$, $J+(f-J)^+\le f+\mathbb E\,v(\cdot-D)-v$
-- statement:
--   Let the demand law $\rho$ on $[0,\infty)$ have positive mean, let $f:\mathbb R\to[0,\infty)$ be continuous, convex, coercive ($f(y)\to\infty$ as $|y|\to\infty$) and nonincreasing on $(-\infty,0]$, and let $K\ge0$. Then there is $J\ge0$ with
--
--   $$\mathcal J_D(f;K)=J,$$
--
--   the single-location value from initial position $0$ over all nonanticipative policies with auxiliary randomness, and there is a measurable $v$ with $-K\le v\le0$ such that
--
--   $$J+(f(y)-J)^+\le f(y)+\mathbb E\,v(y-D)-v(y)\qquad(y\in\mathbb R).$$
--
--   This is the accounting inequality (5) of Lemma 1 (with $u$ equal to $v$ up to a constant, so $\mathrm{osc}(u)\le K$), together with the identification of $J$ as the single-location value. The monotonicity on $(-\infty,0]$ holds for every cost the source uses: $F_i$ and $f_{L_0}$ equal $p$ times the expected backlog at negative positions.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 1, Section 4.1, p. 11 (equations (5) and (6)), and Appendix A (proof of Lemma 1); used in Steps 2 and 3 of the proof of Proposition 3, Section 5.3, pp. 24-25.

import Definitions.Def_owmr_single_location

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem sl_subsolution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (f : ℝ → ℝ) (hfc : Continuous f)
    (hfcv : ConvexOn ℝ Set.univ f) (hf0 : ∀ y, 0 ≤ f y)
    (hfco : ∀ C : ℝ, ∃ R : ℝ, ∀ y, R ≤ |y| → C ≤ f y)
    (hfa : AntitoneOn f (Set.Iic 0)) (K : ℝ) (hK : 0 ≤ K) :
    ∃ J : ℝ, 0 ≤ J ∧ slValue ρ f K = ENNReal.ofReal J ∧
      ∃ v : ℝ → ℝ, Measurable v ∧ (∀ y, -K ≤ v y ∧ v y ≤ 0) ∧
        ∀ y, J + max (f y - J) 0 ≤ f y + ∫ d, v (y - (d : ℝ)) ∂ρ - v y := by sorry
end OWMR
