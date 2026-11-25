-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_det_ne_of_mem_Jset
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.det_ne_of_mem_Jset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:42.743334+00:00
-- url     : https://prove2.me/theorems/3d781fac-6aa3-4f51-9193-4bcf9af3a268
-- title:
--   Psi Volume: det ne of mem Jset
-- statement:
--   The Psi Volume construction uses the det ne of mem Jset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L46-L49

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

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.det_ne_of_mem_Jset {a : ℕ} {J' : Subgroup (GL (Fin a) F)} {Y : Matrix (Fin a) (Fin a) F}
    (h : Y ∈ Jset J') : Y.det ≠ 0 := by sorry
