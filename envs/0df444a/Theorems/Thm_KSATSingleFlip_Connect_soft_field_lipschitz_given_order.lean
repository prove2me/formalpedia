-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_lipschitz_given_order
-- name    : KSATSingleFlip.Connect.soft_field_lipschitz_given_order
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:27:19.460235+00:00
-- url     : https://prove2.me/theorems/2fecf295-be66-45a1-9d11-c0262b2b5312
-- title:
--   Lemma 4.5 potential inequality assuming update-order comparison
-- statement:
--   For finite soft-field measures with finite unfrozen mass, assume ν′ is below ν in the paper’s concave-test order and their Poisson updates are also ordered. Then the potential increment after the update is nonnegative and at most β exp(h(ν))(h(ν)−h(ν′)). This proves the quantitative inequality (4.9) conditional on the order-preservation statement, which remains to be established.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, equation (4.9) in Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Mathlib
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_field_lipschitz_given_order (ν' ν : Measure ℝ) [IsFiniteMeasure ν'] [IsFiniteMeasure ν] (β : ℝ) (hβ : 0 ≤ β)
    (hu' : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞)
    (hu : (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞)
    (hord : softFieldLE ν' ν) (hord' : softFieldLE (Rbeta β ν') (Rbeta β ν)) :
    0 ≤ hPot (Rbeta β ν)-hPot (Rbeta β ν') ∧
      hPot (Rbeta β ν)-hPot (Rbeta β ν') ≤ β*Real.exp (hPot ν)*(hPot ν-hPot ν') := by sorry
