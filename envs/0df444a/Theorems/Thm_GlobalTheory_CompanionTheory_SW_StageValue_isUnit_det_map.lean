-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_isUnit_det_map
-- name    : GlobalTheory.CompanionTheory.SW.StageValue.isUnit_det_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:59.303365+00:00
-- url     : https://prove2.me/theorems/e060ec92-95ea-420a-abbb-291a29aa3b0a
-- title:
--   Stage Value: is Unit det map
-- statement:
--   The Stage Value construction uses the is Unit det map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L78-L82

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_StageData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberConsProductSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageValue
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StageValue.isUnit_det_map (T : Matrix (Fin n) (Fin n) E) (hdet : T.det ≠ 0) :
    IsUnit (T.map (inclR (F := F) R)).det := by sorry
