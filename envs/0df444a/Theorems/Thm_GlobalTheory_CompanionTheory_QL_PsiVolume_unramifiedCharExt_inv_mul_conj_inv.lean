-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_PsiVolume_unramifiedCharExt_inv_mul_conj_inv
-- name    : GlobalTheory.CompanionTheory.QL.PsiVolume.unramifiedCharExt_inv_mul_conj_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:09.690735+00:00
-- url     : https://prove2.me/theorems/bd0ce5a1-2402-5edf-ae5f-cc9331850601
-- title:
--   Psi Volume: unramified Char Ext inv mul conj inv
-- statement:
--   The Psi Volume construction uses the unramified Char Ext inv mul conj inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/WeilIntegralUnipotentLeviFormula.lean#L40-L44

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

theorem GlobalTheory.CompanionTheory.QL.PsiVolume.unramifiedCharExt_inv_mul_conj_inv {δ : Fˣ →* ℂˣ} (hδ : ∀ x, ‖((δ x : ℂˣ) : ℂ)‖ = 1) {a : F} (ha : a ≠ 0) :
    (chi0 δ a)⁻¹ * conj ((chi0 δ a)⁻¹) = 1 := by sorry
