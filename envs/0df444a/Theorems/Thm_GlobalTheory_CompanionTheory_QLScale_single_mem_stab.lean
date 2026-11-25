-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLScale_single_mem_stab
-- name    : GlobalTheory.CompanionTheory.QLScale.single_mem_stab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:08:38.218451+00:00
-- url     : https://prove2.me/theorems/a0e9d8c0-57b7-5261-820c-ee783f468011
-- title:
--   QLScale: single mem stab
-- statement:
--   The QLScale construction uses the single mem stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L318-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MatrixHaarRightTranslate.lean#L318-L342

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

theorem GlobalTheory.CompanionTheory.QLScale.single_mem_stab (hLF : LF O ϖ nrm q) {n m : ℕ} [BorelSpace (Matrix (Fin n) (Fin m) F)]
    {dx : Measure (Matrix (Fin n) (Fin m) F)}
    (hinv : dx.IsAddLeftInvariant) (h1 : dx (intMat O n m) = 1) (j : Fin m) :
    dg (Pi.mulSingle j (Units.mk0 ϖ hLF.ne)) ∈ stab nrm dx := by sorry
