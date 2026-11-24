-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_comap_isMaximal
-- name    : GlobalTheory.CompanionTheory.SW.UnitRep.comap_isMaximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:42.445528+00:00
-- url     : https://prove2.me/theorems/a0c1a109-829d-4638-9a6e-27ec0b33cf75
-- title:
--   Unit Rep: comap is Maximal
-- statement:
--   The Unit Rep construction uses the comap is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L89-L91

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

theorem GlobalTheory.CompanionTheory.SW.UnitRep.comap_isMaximal (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) (P : Ideal A) (hP : P.IsMaximal) :
    (P.comap σ).IsMaximal := by sorry
