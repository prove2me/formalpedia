-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_setIntegral_compact_eq_zero
-- name    : GlobalTheory.eq_zero_of_setIntegral_compact_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:18:54.505027+00:00
-- url     : https://prove2.me/theorems/f9ed4fe2-d446-4f5e-86d3-363ce3e2ca35
-- title:
--   Global Theory: eq zero of set Integral compact eq zero
-- statement:
--   The Global Theory construction uses the eq zero of set Integral compact eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContDensityOnEqFibreMass.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContDensityOnEqFibreMass.lean#L8-L42

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContDensityOnEqFibreMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory

theorem GlobalTheory.eq_zero_of_setIntegral_compact_eq_zero {K : Type} [MetricSpace K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasureOnCompacts ν]
    [ν.IsOpenPosMeasure] {B : Set K} (hB : IsOpen B) {h : K → ℂ} (hc : ContinuousOn h B)
    (hz : ∀ S : Set K, IsCompact S → S ⊆ B → ∫ b in S, h b ∂ν = 0) {t : K} (ht : t ∈ B) :
    h t = 0 := by sorry
