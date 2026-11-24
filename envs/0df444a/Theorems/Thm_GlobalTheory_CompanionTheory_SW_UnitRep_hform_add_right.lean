-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_add_right
-- name    : GlobalTheory.CompanionTheory.SW.UnitRep.hform_add_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:53.543542+00:00
-- url     : https://prove2.me/theorems/87049b6c-addc-41ff-9fe6-23c390f330c2
-- title:
--   Unit Rep: hform add right
-- statement:
--   The Unit Rep construction uses the hform add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormRepresentsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitRep
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.CompanionTheory.SW.UnitRep.hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by sorry
