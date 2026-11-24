-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_hform_single_single
-- name    : GlobalTheory.CompanionTheory.SW.UnitRep.hform_single_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:12.140299+00:00
-- url     : https://prove2.me/theorems/a82dea70-5848-4990-bf97-ee19f38e6211
-- title:
--   Unit Rep: hform single single
-- statement:
--   The Unit Rep construction uses the hform single single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L28-L35

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

theorem GlobalTheory.CompanionTheory.SW.UnitRep.hform_single_single (σ : A →+* A) (J : Matrix n n A) (i j : n) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by sorry
