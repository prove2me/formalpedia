-- Prove2me | Theorems.Thm_GlobalTheory_T_local_field_selfdual_measure_exists
-- name    : GlobalTheory.T.local_field_selfdual_measure_exists
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:40:31.577035+00:00
-- url     : https://prove2.me/theorems/449d2303-b362-5e71-980b-5993d099d6a9
-- title:
--   T: local field selfdual measure exists
-- statement:
--   The T construction uses the local field selfdual measure exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExistsStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExistsStatement.lean#L8-L9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExistsStatement
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

theorem GlobalTheory.T.local_field_selfdual_measure_exists : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (ψ : AddChar K Circle), Continuous ψ → ψ ≠ 1 → SelfDual (GroundTheory.LocalField.selfDualMeasure ψ) (fun s t => ((ψ (s * t) : Circle) : ℂ)) := by sorry
