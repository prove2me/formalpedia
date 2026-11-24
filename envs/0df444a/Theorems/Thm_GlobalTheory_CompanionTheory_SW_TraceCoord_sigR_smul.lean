-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_sigR_smul
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.sigR_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:15.149979+00:00
-- url     : https://prove2.me/theorems/d7b7ab21-9b5d-4bfd-9428-58d0cae5683b
-- title:
--   Trace Coord: sig R smul
-- statement:
--   The Trace Coord construction uses the sig R smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L98-L103

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.sigR_smul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (r : R) (a : R ⊗[F] E) :
    sigR R σ (r • a) = r • sigR R σ a := by sorry
