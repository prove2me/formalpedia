-- Prove2me | Theorems.Thm_GlobalTheory_DirichletDeriv_rpow_neg_le
-- name    : GlobalTheory.DirichletDeriv.rpow_neg_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:42.290902+00:00
-- url     : https://prove2.me/theorems/9e94f818-7dd1-4a88-a1c1-8549515bb6e6
-- title:
--   Dirichlet Deriv: rpow neg le
-- statement:
--   The Dirichlet Deriv construction uses the rpow neg le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsNormDerivLFunctionLe.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsNormDerivLFunctionLe.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionEqTsumOfOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsNormDerivLFunctionLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.DirichletDeriv

theorem GlobalTheory.DirichletDeriv.rpow_neg_le {q n : ℕ} (hn : 1 ≤ n) (hnq : n ≤ q) {x : ℝ}
    (hx : 1 - 2 / Real.log (3 * q) ≤ x) : (n : ℝ) ^ (-x) ≤ Real.exp 2 * (n : ℝ)⁻¹ := by sorry
