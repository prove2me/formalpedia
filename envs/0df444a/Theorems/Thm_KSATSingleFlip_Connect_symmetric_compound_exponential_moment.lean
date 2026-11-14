-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_symmetric_compound_exponential_moment
-- name    : KSATSingleFlip.Connect.symmetric_compound_exponential_moment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:44:29.598414+00:00
-- url     : https://prove2.me/theorems/0cd668e6-8cd9-4ead-bb19-0b74f251ea40
-- title:
--   Exponential transform of the symmetrized compound Poisson law
-- statement:
--   For a finite intensity measure whose exponential moments at c and −c are finite, the exponential moment of X−X′ for independent compound Poisson copies is the product of their two explicit compound-Poisson transforms. This is the transform of the kernel Kν in Definition 4.2.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and equation (4.3), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.symmetric_compound_exponential_moment (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ)
    (hp : (∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ) ≠ ∞)
    (hm : (∫⁻ x, ENNReal.ofReal (Real.exp ((-c)*x)) ∂μ) ≠ ∞) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (c*z)) ∂(compoundPoisson μ ∗ Measure.map (fun z : ℝ => -z) (compoundPoisson μ))) =
      ENNReal.ofReal (Real.exp (-(μ Set.univ).toReal) * Real.exp ((∫⁻ x, ENNReal.ofReal (Real.exp (c*x)) ∂μ).toReal) *
        (Real.exp (-(μ Set.univ).toReal) * Real.exp ((∫⁻ x, ENNReal.ofReal (Real.exp ((-c)*x)) ∂μ).toReal))) := by sorry
