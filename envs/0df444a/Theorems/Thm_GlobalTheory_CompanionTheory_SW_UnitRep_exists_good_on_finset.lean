-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitRep_exists_good_on_finset
-- name    : GlobalTheory.CompanionTheory.SW.UnitRep.exists_good_on_finset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:10:43.238786+00:00
-- url     : https://prove2.me/theorems/86c94290-0791-4b1a-8e58-b9ed6651bf8f
-- title:
--   Unit Rep: exists good on finset
-- statement:
--   The Unit Rep construction uses the exists good on finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L100-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormRepresentsUnit.lean#L100-L169

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

theorem GlobalTheory.CompanionTheory.SW.UnitRep.exists_good_on_finset [Finite (MaximalSpectrum A)] (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y)
    (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ) (m : ℕ)
    (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (hJ : ∀ i j, σ (J j i) = J i j)
    (hdet : IsUnit J.det) (T : Finset (MaximalSpectrum A)) :
    ∃ x, ∀ p ∈ T, hform σ J x x ∉ p.asIdeal := by sorry
