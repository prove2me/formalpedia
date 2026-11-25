-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_blocks_mul_pEl
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.blocks_mul_pEl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:29.528003+00:00
-- url     : https://prove2.me/theorems/deab0ae6-4d24-55cf-9684-732664e7c73a
-- title:
--   Psi Volume: blocks mul p El
-- statement:
--   The Psi Volume construction uses the blocks mul p El property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L17-L38

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

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.blocks_mul_pEl {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F)
    (B : Matrix (Fin r) (Fin c) F) (m : GL (Fin c) F) :
    bAA (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = bAA x ∧
    bDA (x * (pEl 1 B m : GL (Fin (r + c)) F).val) = bDA x ∧
    bAD (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
      bAA x * B + bAD x * (m : Matrix (Fin c) (Fin c) F) ∧
    bDD (x * (pEl 1 B m : GL (Fin (r + c)) F).val) =
      bDA x * B + bDD x * (m : Matrix (Fin c) (Fin c) F) := by sorry
