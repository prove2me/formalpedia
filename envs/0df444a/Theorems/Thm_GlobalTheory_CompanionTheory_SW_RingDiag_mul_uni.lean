-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_mul_uni
-- name    : GlobalTheory.CompanionTheory.SW.RingDiag.mul_uni
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:16.062678+00:00
-- url     : https://prove2.me/theorems/82545dae-c1c7-4785-9fc7-18c9181e39f6
-- title:
--   Ring Diag: mul uni
-- statement:
--   The Ring Diag construction uses the mul uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L70-L75

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

theorem GlobalTheory.CompanionTheory.SW.RingDiag.mul_uni (K : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (r : Fin m → A) (i : Fin (m + 1)) :
    (K * uni r) i 0 = K i 0 ∧ ∀ j : Fin m, (K * uni r) i j.succ = K i j.succ + K i 0 * r j := by sorry
