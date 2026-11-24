-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_cT_bd
-- name    : GlobalTheory.CompanionTheory.SW.RingDiag.cT_bd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:35.382065+00:00
-- url     : https://prove2.me/theorems/44fa9e01-b992-45ba-a4d0-22ec595c0145
-- title:
--   Ring Diag: c T bd
-- statement:
--   The Ring Diag construction uses the c T bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L38-L42

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinatePolynomialsFormMemKernelDifferential
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianUnitFormDiagonalizes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RingDiag
open HeckeCharacterZeroLocus.SiegelWeilU
variable {A : Type} [CommRing A] {m : ℕ}

theorem GlobalTheory.CompanionTheory.SW.RingDiag.cT_bd (σ : A →+* A) (a : A) (M : Matrix (Fin m) (Fin m) A) :
    cT σ (bd a M) = bd (σ a) (cT σ M) := by sorry
