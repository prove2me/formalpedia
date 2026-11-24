-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_mul
-- name    : GlobalTheory.CompanionTheory.SW.RingDiag.bd_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:05.041386+00:00
-- url     : https://prove2.me/theorems/3449afbc-69fd-43a7-b741-b33467cce0db
-- title:
--   Ring Diag: bd mul
-- statement:
--   The Ring Diag construction uses the bd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L26-L30

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

theorem GlobalTheory.CompanionTheory.SW.RingDiag.bd_mul (a b : A) (M N : Matrix (Fin m) (Fin m) A) :
    bd a M * bd b N = bd (a * b) (M * N) := by sorry
