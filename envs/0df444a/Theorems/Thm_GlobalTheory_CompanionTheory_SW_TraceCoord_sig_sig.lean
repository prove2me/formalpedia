-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_sig_sig
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.sig_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:33.07746+00:00
-- url     : https://prove2.me/theorems/30620f2b-953b-4d9d-a750-3cadee280e87
-- title:
--   Trace Coord: sig sig
-- statement:
--   The Trace Coord construction uses the sig sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L139-L142

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.sig_sig (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by sorry
