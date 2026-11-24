-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_continuous_fstA
-- name    : GlobalTheory.CompanionTheory.SW.MeasProj.continuous_fstA
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:07:45.866436+00:00
-- url     : https://prove2.me/theorems/19972037-a573-43e8-9f3d-8f11db785f81
-- title:
--   Meas Proj: continuous fst A
-- statement:
--   The Meas Proj construction uses the continuous fst A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean#L54-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean#L54-L54

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.MeasProj.continuous_fstA : Continuous (fstA F) := by sorry
