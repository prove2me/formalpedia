-- Prove2me | Theorems.Thm_ItoLemma_ito_formula_time_dependent_bounded
-- name    : ItoLemma.ito_formula_time_dependent_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:52:45.322681+00:00
-- url     : https://prove2.me/theorems/3ed2c9dc-9428-4b3d-bbd2-b97054e4e09e
-- title:
--   Time-Dependent Itô Formula for a Bounded Brownian Diffusion
-- statement:
--   On a probability space carrying Brownian motion W with a Brownian filtration, let X be a continuous adapted version of the scalar Itô process Xₜ=x₀+∫₀ᵗ μ_s ds+∫₀ᵗ σ_s dW_s with bounded measurable progressively measurable drift and diffusion and finite diffusion energy. Let f(t,x) possess continuous time derivative f_t and continuous first and second spatial derivatives f_x,f_xx, with a common finite absolute bound. Suppose the resulting f_x(t,Xₜ)σ_t integrand is measurable, progressive and square-integrable. Then for each deterministic t≥0 the random variables f(t,Xₜ)-f(0,x₀) and ∫₀ᵗ[f_t(s,X_s)+μ_s f_x(s,X_s)+½σ_s² f_xx(s,X_s)]ds+∫₀ᵗσ_s f_x(s,X_s)dW_s are equal almost surely. This is the genuine scalar C¹,² Itô formula. The process representation does not assume the chain rule conclusion.
-- source:
--   Wikipedia contributors, Itô's lemma, https://en.wikipedia.org/wiki/It%C3%B4%27s_lemma (accessed 26 October 2026), scalar time-dependent diffusion case. The formal statement uses the accepted Prove2Me LevyStochCalc Brownian stochastic-integral interface and deliberately stages bounded coefficients and derivatives. Related existing multivariate time-independent vector formula UUID 550fc0f9-7957-4075-b3fb-68172654fce1 and broader continuous-semimartingale Open theorem EthierKurtz.ito_formula UUID 3ce50ab9-1611-4ba3-b900-6388eec002bf.

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoVersionExists
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal

universe u

/-- The bounded-coefficient scalar C¹,² Itô formula at each deterministic
nonnegative time. The process is specified by its drift–Brownian-integral
decomposition, continuity and adaptedness. -/

theorem ItoLemma.ito_formula_time_dependent_bounded
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    (x₀ : ℝ) (μ σ : Ω → ℝ → ℝ)
    (hμm : Measurable (Function.uncurry μ))
    (hμp : Probability.ProgressivelyMeasurable ℱ μ)
    (hσm : Measurable (Function.uncurry σ))
    (hσp : Probability.ProgressivelyMeasurable ℱ σ)
    (hσq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖σ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hμbd : ∀ ω s, |μ ω s| ≤ C)
    (hσbd : ∀ ω s, |σ ω s| ≤ C)
    (X : ℝ → Ω → ℝ)
    (hXcont : ∀ ω, Continuous fun t => X t ω)
    (hXadapt : ∀ t, Measurable[ℱ t] (X t))
    (hXrep : ∀ t : ℝ, 0 ≤ t →
      (fun ω => X t ω) =ᵐ[P]
        (fun ω => x₀ + (∫ s in Set.Icc (0 : ℝ) t, μ ω s ∂volume) +
          stochasticIntegralBrownian W ℱ hℱ σ hσm hσp hσq t ω))
    (f ft fx fxx : ℝ → ℝ → ℝ)
    (hft : ∀ t x, HasDerivAt (fun r => f r x) (ft t x) t)
    (hfx : ∀ t x, HasDerivAt (fun y => f t y) (fx t x) x)
    (hfxx : ∀ t x, HasDerivAt (fun y => fx t y) (fxx t x) x)
    (hftc : Continuous (Function.uncurry ft))
    (hfxc : Continuous (Function.uncurry fx))
    (hfxxc : Continuous (Function.uncurry fxx))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hfbd : ∀ t x, |ft t x| ≤ K ∧ |fx t x| ≤ K ∧ |fxx t x| ≤ K)
    (hJm : Measurable (Function.uncurry fun ω s => fx s (X s ω) * σ ω s))
    (hJp : Probability.ProgressivelyMeasurable ℱ
      (fun ω s => fx s (X s ω) * σ ω s))
    (hJq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖fx s (X s ω) * σ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun ω => f t (X t ω) - f 0 x₀) =ᵐ[P] fun ω =>
      (∫ s in Set.Ioc (0 : ℝ) t,
        (ft s (X s ω) + μ ω s * fx s (X s ω) +
          (1 / 2 : ℝ) * (σ ω s) ^ 2 * fxx s (X s ω)) ∂volume) +
      stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => fx s (X s ω) * σ ω s) hJm hJp hJq t ω := by sorry
