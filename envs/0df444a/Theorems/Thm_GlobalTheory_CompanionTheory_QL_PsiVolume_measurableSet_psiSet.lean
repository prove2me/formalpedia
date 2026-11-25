-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_measurableSet_psiSet
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.measurableSet_psiSet
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:14.086344+00:00
-- url     : https://prove2.me/theorems/20493eae-8d70-42f9-a0a5-722a0572a6c0
-- title:
--   Psi Volume: measurable Set psi Set
-- statement:
--   The Psi Volume construction uses the measurable Set psi Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L118-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L118-L142

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MatrixAdditiveHaarNormalizedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MeasureInvertibleIntegralMatricesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_WeilIntegralUnipotentLeviFormula
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.PsiVolume
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.measurableSet_psiSet (hLF : LF O ϖ nrm q) {r d c : ℕ} (B : Matrix (Fin r) (Fin c) F)
    (m : GL (Fin c) F) :
    MeasurableSet (psiSet O ϖ B m : Set (Matrix (Fin (r + d)) (Fin (r + c)) F)) := by sorry
