-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_cT_cT
-- name    : GlobalTheory.CompanionTheory.SW.RingDiag.cT_cT
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:50.36815+00:00
-- url     : https://prove2.me/theorems/b9db0861-234f-421f-b550-9825939a73e4
-- title:
--   Ring Diag: c T c T
-- statement:
--   The Ring Diag construction uses the c T c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L113-L115

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

theorem GlobalTheory.CompanionTheory.SW.RingDiag.cT_cT (σ : A →+* A) (hσ : ∀ y, σ (σ y) = y) {p q : Type}
    (M : Matrix p q A) : cT σ (cT σ M) = M := by sorry
