-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceCoord_gramB_tensor
-- name    : GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_tensor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:33.718052+00:00
-- url     : https://prove2.me/theorems/e1350ef4-e2df-4cf9-8eaa-deda0601a581
-- title:
--   Trace Coord: gram B tensor
-- statement:
--   The Trace Coord construction uses the gram B tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L114-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ExistsTraceFormGramMatrixInBasis.lean#L114-L124

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

theorem GlobalTheory.CompanionTheory.SW.TraceCoord.gramB_tensor (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] {d M : ℕ}
    (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) :
    gramB (sigR R σ) (Algebra.TensorProduct.basis R b) (JR R J) =
      (gramB (σ : E →+* E) b J).map (algebraMap F R) := by sorry
