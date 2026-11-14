-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_threshold_strict_upper_if_order_preserved
-- name    : KSATSingleFlip.Connect.soft_field_threshold_strict_upper_if_order_preserved
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:12:38.402149+00:00
-- url     : https://prove2.me/theorems/10050d39-04a9-45a9-be18-c8e23e67f387
-- title:
--   Strict k-SAT threshold upper bound, conditional on Poisson comparison
-- statement:
--   Assume the Poisson update preserves the concave-test order on symmetric measures with finite unfrozen mass. Then γ* ≤ 1 − (1−c₀)e⁻¹/2 < 1. This establishes the strict upper bound in Theorem 4.4 conditional on the still-open order-preservation assertion in Lemma 4.5.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 4.5 and Theorem 4.4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_threshold_strict_upper_if_order_preserved
    (hpres : ∀ (β : ℝ) (ν' ν : Measure ℝ), 0 ≤ β →
      Measure.map (fun z : ℝ => -z) ν' = ν' →
      Measure.map (fun z : ℝ => -z) ν = ν →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞ →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞ →
      softFieldLE ν' ν → softFieldLE (Rbeta β ν') (Rbeta β ν)) :
    gammaStar ≤ 1 - (1-c0)*Real.exp (-1)/2 ∧ gammaStar < 1 := by sorry
