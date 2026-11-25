-- Prove2me | Theorems.Thm_GlobalTheory_T_gaussian_iteratedFDeriv_weighted_exp_bounded
-- name    : GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:54.750869+00:00
-- url     : https://prove2.me/theorems/8decb7f0-dab2-4f00-8709-c3fc8b877350
-- title:
--   T: gaussian iterated FDeriv weighted exp bounded
-- statement:
--   The T construction uses the gaussian iterated FDeriv weighted exp bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBoundedStatement.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GaussianIteratedFDerivWeightedExpBoundedStatement.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianIteratedFDerivWeightedExpBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c α : ℝ), 0 < c → α < 1 → ∀ (k m : ℕ),
    ∃ K : ℝ, ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
      Real.exp (c * α * ‖y‖ ^ 2) ≤ K := by sorry
