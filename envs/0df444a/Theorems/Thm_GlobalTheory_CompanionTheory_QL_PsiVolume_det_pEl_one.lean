-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_det_pEl_one
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.det_pEl_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:00.376701+00:00
-- url     : https://prove2.me/theorems/69925ba1-35ee-4c81-96ea-59b18d4e95a8
-- title:
--   Psi Volume: det p El one
-- statement:
--   The Psi Volume construction uses the det p El one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L87-L91

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
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.det_pEl_one {r c : ℕ} (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    Matrix.GeneralLinearGroup.det (pEl 1 B m : GL (Fin (r + c)) F) =
      Matrix.GeneralLinearGroup.det m := by sorry
