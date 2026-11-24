-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_gramB_symm
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_symm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:15.608806+00:00
-- url     : https://prove2.me/theorems/6d0f2065-7c09-4a07-98de-2da481c3a1bc
-- title:
--   Trace Coord: gram B symm
-- statement:
--   The Trace Coord construction uses the gram B symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L144-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L144-L156

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_symm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).IsSymm := by sorry
