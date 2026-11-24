-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageValue_one_tmul_algebraMap
-- name    : GlobalTheory.CompanionTheory.SW.StageValue.one_tmul_algebraMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:11:28.988274+00:00
-- url     : https://prove2.me/theorems/876b1708-dd7f-4d56-9ed1-58495d133450
-- title:
--   Stage Value: one tmul algebra Map
-- statement:
--   The Stage Value construction uses the one tmul algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramFiberConsProductSupport.lean#L15-L18

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

theorem GlobalTheory.CompanionTheory.SW.StageValue.one_tmul_algebraMap (t : F) :
    (1 : R) ⊗ₜ[F] (algebraMap F E t) = (algebraMap F R t) ⊗ₜ[F] (1 : E) := by sorry
