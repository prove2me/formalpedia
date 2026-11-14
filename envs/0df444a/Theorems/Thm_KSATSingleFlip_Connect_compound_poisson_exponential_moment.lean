-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_exponential_moment
-- name    : KSATSingleFlip.Connect.compound_poisson_exponential_moment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:43:15.196018+00:00
-- url     : https://prove2.me/theorems/375526ed-e61e-4dac-9dd7-70ba841be373
-- title:
--   Exponential transform of the compound Poisson soft-field law
-- statement:
--   For a finite intensity measure μ and a real c whose exponential moment is finite, the compound Poisson law defined for the soft-field recursion has extended exponential moment exp(−μ(ℝ)) exp(∫e^{cx} μ(dx)). This is an exact transform of the concrete convolution-series definition.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.compound_poisson_exponential_moment (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ)
    (hmom : (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ) ≠ ∞) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂(compoundPoisson μ)) =
      ENNReal.ofReal (Real.exp (-(μ Set.univ).toReal) *
        Real.exp ((∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ).toReal)) := by sorry
