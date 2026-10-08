-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_survival_eq_exp_neg_integral
-- name    : LariviereIGFR.Moments.survival_eq_exp_neg_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:59.541055+00:00
-- url     : https://prove2.me/theorems/0f1112fe-1d2f-41ca-af88-56212c19b718
-- title:
--   Proof of Theorem 2, p. 603 — Φ̄(ξ) = exp[−∫₀^ξ h(s) ds] (Ross 1983)
-- statement:
--   Let $X\ge 0$ have law $\mu$ with regular density $\phi$, survival function $\bar\Phi$ and failure rate $h=\phi/\bar\Phi$. For every $\xi\ge 0$ with $\Phi(\xi)<1$,
--   $$
--   \bar\Phi(\xi)=\exp\Big[-\int_0^\xi h(s)\,ds\Big].
--   $$
--
--   The survival function is recovered from the failure rate; the paper uses this representation (citing Ross 1983) to turn pointwise bounds on $h$ into bounds on $\bar\Phi$, and hence into stochastic comparisons with Pareto laws.
--
--   **Formalization Note** The integral is the interval (Bochner) integral of $h$ over $[0,\xi]$; on that interval $\bar\Phi\ge\bar\Phi(\xi)>0$, so $0\le h\le\phi/\bar\Phi(\xi)$ there, $h$ is integrable and the integral is not a junk value. The regular-density pin makes $h=0$ to the left of the support.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3, proof of Theorem 2, first paragraph (citing Ross 1983)

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 2, p. 603 (citing Ross 1983): `Φ̄(ξ) = exp(-∫₀^ξ h(s) ds)` for every `ξ ≥ 0`
with `Φ(ξ) < 1`. -/
theorem survival_eq_exp_neg_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : LariviereIGFR.Char.IsRegDensity μ φ) :
    ∀ ξ, 0 ≤ ξ → cdf μ ξ < 1 →
      LariviereIGFR.Char.survival μ ξ = Real.exp (-∫ s in (0 : ℝ)..ξ, LariviereIGFR.Char.failureRate μ φ s) := by sorry

end LariviereIGFR.Moments
