-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_diagonalise
-- name    : GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:10:21.510012+00:00
-- url     : https://prove2.me/theorems/9068b2d8-e737-45d2-a610-715b5069fbd8
-- title:
--   Ring Diag: diagonalise
-- statement:
--   The Ring Diag construction uses the diagonalise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L141-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianUnitFormDiagonalizes.lean#L141-L191

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

theorem GlobalTheory.CompanionTheory.SW.RingDiag.diagonalise : ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A), (∀ y, σ (σ y) = y) → (∀ (m : ℕ) (J : Matrix (Fin (m + 1)) (Fin (m + 1)) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ x, IsUnit (HeckeCharacterZeroLocus.SiegelWeilU.hform σ J x x)) → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) A), (∀ i j, σ (J j i) = J i j) → IsUnit J.det → ∃ (g : Matrix (Fin m) (Fin m) A) (d : Fin m → A), IsUnit g.det ∧ (∀ i, IsUnit (d i) ∧ σ (d i) = d i) ∧ HeckeCharacterZeroLocus.SiegelWeilU.cT σ g * J * g = Matrix.diagonal d := by sorry
