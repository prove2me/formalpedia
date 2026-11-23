-- Prove2me | Theorems.Thm_GlobalTheory_LLeft_norm_term_le
-- name    : GlobalTheory.LLeft.norm_term_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:27.264832+00:00
-- url     : https://prove2.me/theorems/5be9824a-a74c-496f-b654-96371fae6b93
-- title:
--   LLeft: norm term le
-- statement:
--   The LLeft construction uses the norm term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L190-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SummableNinePowMulInvSqSucc.lean#L190-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNinePowMulInvSqSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open GlobalTheory.LLeft

theorem GlobalTheory.LLeft.norm_term_le (b : ℕ → ℂ) (K R : ℝ) (hb : ∀ n, ‖b n‖ ≤ K) (s : ℂ)
    (hs : -(15 / 8 : ℝ) ≤ s.re) (hR : ‖s‖ ≤ R) (n : ℕ) :
    ‖b n * diffPow 3 s ((n : ℝ) + 1)‖ ≤ K * (R + 3) ^ 3 * ((n : ℝ) + 1) ^ (-(9 / 8 : ℝ)) := by sorry
