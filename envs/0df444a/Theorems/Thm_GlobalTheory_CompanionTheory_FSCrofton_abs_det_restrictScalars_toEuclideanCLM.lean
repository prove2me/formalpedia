-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_abs_det_restrictScalars_toEuclideanCLM
-- name    : GlobalTheory.CompanionTheory.FSCrofton.abs_det_restrictScalars_toEuclideanCLM
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:48.991177+00:00
-- url     : https://prove2.me/theorems/b3144a95-ef2f-4fca-a6d7-547566a23a91
-- title:
--   FSCrofton: abs det restrict Scalars to Euclidean CLM
-- statement:
--   The FSCrofton construction uses the abs det restrict Scalars to Euclidean CLM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCount.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCount.lean#L16-L24

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton

theorem GlobalTheory.CompanionTheory.FSCrofton.abs_det_restrictScalars_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det| =
      ‖M.det‖ ^ 2 := by sorry
