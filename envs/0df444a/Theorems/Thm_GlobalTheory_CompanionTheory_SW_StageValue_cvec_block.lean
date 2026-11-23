-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_cvec_block
-- name    : GlobalTheory.CompanionTheory.SW.StageValue.cvec_block
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:00.282305+00:00
-- url     : https://prove2.me/theorems/a0cecb7c-eb2f-4ecf-9c5f-2419f2a8f7e6
-- title:
--   Stage Value: cvec block
-- statement:
--   The Stage Value construction uses the cvec block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L54-L57

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

theorem GlobalTheory.CompanionTheory.SW.StageValue.cvec_block (T : Matrix (Fin n) (Fin n) E) :
    cvec R t a ((blockOne (algebraMap F E t) T).map (inclR R)) = 0 := by sorry
