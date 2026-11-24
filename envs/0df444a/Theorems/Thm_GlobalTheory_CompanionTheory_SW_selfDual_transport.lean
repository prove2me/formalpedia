-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_selfDual_transport
-- name    : GlobalTheory.CompanionTheory.SW.selfDual_transport
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:52.380819+00:00
-- url     : https://prove2.me/theorems/c9062240-ccaf-4b27-ad4e-bfd2fbea2ef2
-- title:
--   SW: self Dual transport
-- statement:
--   The SW construction uses the self Dual transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SelfdualMeasureTransportEquiv.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SelfdualMeasureTransportEquiv.lean#L34-L47

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTransportEquiv
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.selfDual_transport (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by sorry
