-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_RatCoord_cv_act
-- name    : GlobalTheory.CompanionTheory.SW.BB.RatCoord.cv_act
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:01:26.829799+00:00
-- url     : https://prove2.me/theorems/0dbc9b7b-6506-4b2b-b064-85e5a5075537
-- title:
--   Rat Coord: cv act
-- statement:
--   The Rat Coord construction uses the cv act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteComponentCoordinatesAction.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteComponentCoordinatesAction.lean#L36-L45

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteComponentCoordinatesAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.BB.RatCoord.cv_act (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {d M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E) (h : HA R σ J)
    (x : Fin M × Fin d → F) :
    cv R b (actW R σ J h (ratTup R (ofF b x)) 0) =
      gmat R σ J b h *ᵥ fun j => algebraMap F R (x j) := by sorry
