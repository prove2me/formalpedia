-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_clm_apply_eq_sum
-- name    : GlobalTheory.CompanionTheory.FSCrofton.clm_apply_eq_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:24.46456+00:00
-- url     : https://prove2.me/theorems/095ffbae-a78f-420e-8e7c-72cea4f3acff
-- title:
--   FSCrofton: clm apply eq sum
-- statement:
--   The FSCrofton construction uses the clm apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCount.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCount.lean#L11-L14

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

theorem GlobalTheory.CompanionTheory.FSCrofton.clm_apply_eq_sum {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by sorry
