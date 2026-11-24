-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarCoord_hermCoord_add
-- name    : GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:54.502891+00:00
-- url     : https://prove2.me/theorems/609fbe43-0e29-441e-8559-f72759e440be
-- title:
--   Haar Coord: herm Coord add
-- statement:
--   The Haar Coord construction uses the herm Coord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L159-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHaarMeasure.lean#L159-L165

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R]

theorem GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_add (σ : E →ₐ[F] E) (n : ℕ) (S T : HermR R σ n) :
    hermCoord R σ n (S + T) = hermCoord R σ n S + hermCoord R σ n T := by sorry
