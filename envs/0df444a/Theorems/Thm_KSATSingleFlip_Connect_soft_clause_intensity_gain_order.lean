-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_soft_clause_intensity_gain_order
-- name    : KSATSingleFlip.Connect.soft_clause_intensity_gain_order
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:41:09.352207+00:00
-- url     : https://prove2.me/theorems/767cd458-ac44-48d6-b5cd-ec185f346579
-- title:
--   Clause-intensity comparison for the single-clause gain
-- statement:
--   If ν′ precedes ν in the paper’s concave-test order, then the integral of the single-clause gain against the corresponding clause-parameter intensity ρν′ is at most its integral against ρν. The gain is extended by zero outside [0,1]. This supplies the derivative-sign comparison in the Poisson interpolation proof of Lemma 4.5; differentiability and the update representation remain separate.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftFieldClauseIntensity
import Mathlib
open MeasureTheory KSATSingleFlip.Connect Set
set_option autoImplicit false

theorem KSATSingleFlip.Connect.soft_clause_intensity_gain_order (ν' ν : Measure ℝ) (hord : softFieldLE ν' ν)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc 0 1)) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    (∫ s, (Icc 0 1).indicator (softClauseGain ψ v0 v1) s ∂(softClauseIntensity ν')) ≤
      ∫ s, (Icc 0 1).indicator (softClauseGain ψ v0 v1) s ∂(softClauseIntensity ν) := by sorry
