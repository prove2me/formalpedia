-- Prove2me | Theorems.Thm_GlobalTheory_T_selfdual_measure_transport_equiv
-- name    : GlobalTheory.T.selfdual_measure_transport_equiv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:54.602222+00:00
-- url     : https://prove2.me/theorems/97eafdba-887a-5f99-b6e5-4b5de3e8f94e
-- title:
--   T: selfdual measure transport equiv
-- statement:
--   The T construction uses the selfdual measure transport equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SelfdualMeasureTransportEquivStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/SelfdualMeasureTransportEquivStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTransportEquiv
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SelfdualMeasureTransportEquivStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.selfdual_measure_transport_equiv : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ), SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by sorry
