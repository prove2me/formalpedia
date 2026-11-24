-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_gramB_det
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:24.133412+00:00
-- url     : https://prove2.me/theorems/40f03b20-2a07-467a-a6d7-2c8c4619c901
-- title:
--   Trace Coord: gram B det
-- statement:
--   The Trace Coord construction uses the gram B det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L158-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L158-L184

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_det (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).det ≠ 0 := by sorry
