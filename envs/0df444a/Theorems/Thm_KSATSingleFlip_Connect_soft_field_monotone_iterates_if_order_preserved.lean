-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_field_monotone_iterates_if_order_preserved
-- name    : KSATSingleFlip.Connect.soft_field_monotone_iterates_if_order_preserved
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:08:40.748776+00:00
-- url     : https://prove2.me/theorems/62eeeef9-4889-48ec-ada6-c56f35b25111
-- title:
--   Conditional monotonicity of the soft-field iterates
-- statement:
--   Assume the Poisson update Rβ preserves the concave-test order on symmetric measures with finite unfrozen mass, for β ≥ 0. Then, for every γ, successive iterates are ordered, the potential h is nondecreasing, and the gap m−h is nondecreasing. These are consequences stated in Lemma 4.5, conditional here on its still-open order-preservation assertion.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldOrder
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect Set
open scoped ENNReal

theorem KSATSingleFlip.Connect.soft_field_monotone_iterates_if_order_preserved
    (hpres : ∀ (β : ℝ) (ν' ν : Measure ℝ), 0 ≤ β →
      Measure.map (fun z : ℝ => -z) ν' = ν' →
      Measure.map (fun z : ℝ => -z) ν = ν →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞ →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞ →
      softFieldLE ν' ν → softFieldLE (Rbeta β ν') (Rbeta β ν))
    (γ : ℝ) : ∀ r : ℕ,
      softFieldLE (nuIter γ r) (nuIter γ (r+1)) ∧
      hPot (nuIter γ r) ≤ hPot (nuIter γ (r+1)) ∧
      ((massM (nuIter γ r)).toReal - hPot (nuIter γ r)) ≤
        ((massM (nuIter γ (r+1))).toReal - hPot (nuIter γ (r+1))) := by sorry
