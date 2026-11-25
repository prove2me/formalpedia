-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_map_eq_smul
-- name    : GlobalTheory.CompanionTheory.QLScale.map_eq_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:33.426448+00:00
-- url     : https://prove2.me/theorems/af5d829c-b612-4fc5-bdf1-51064d0a881c
-- title:
--   QLScale: map eq smul
-- statement:
--   The QLScale construction uses the map eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L91-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L91-L135

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_CartanDecompositionGeneralLinearStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixHaarRightTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLScale
open scoped ENNReal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
variable [MeasurableSpace F] [BorelSpace F]

theorem GlobalTheory.CompanionTheory.QLScale.map_eq_smul (hLF : LF O ϖ nrm q) {n m : ℕ} {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1)
    (φ : Matrix (Fin n) (Fin m) F ≃ₜ+ Matrix (Fin n) (Fin m) F) :
    Measure.map φ dx = dx (φ ⁻¹' intMat O n m) • dx := by sorry
