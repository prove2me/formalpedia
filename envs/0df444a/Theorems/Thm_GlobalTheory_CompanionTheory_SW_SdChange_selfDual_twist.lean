-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_SdChange_selfDual_twist
-- name    : GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:06.558143+00:00
-- url     : https://prove2.me/theorems/ce46ad7c-b1a8-4d6c-a9c4-95bba04e0391
-- title:
--   Sd Change: self Dual twist
-- statement:
--   The Sd Change construction uses the self Dual twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SelfdualMeasureTwistBySymmetricAuto.lean#L9-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SelfdualMeasureTwistBySymmetricAuto.lean#L9-L68

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTwistBySymmetricAuto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SdChange

theorem GlobalTheory.CompanionTheory.SW.SdChange.selfDual_twist : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V),
    (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ →
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by sorry
