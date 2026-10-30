-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutNumerator_centered_rationalDefect_rank_relative
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:48:00.139257+00:00
-- url     : https://prove2.me/theorems/26a2ced7-9a43-46ef-b3d0-2cbe6e8476d2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutNumeratorBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutNumeratorBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator`, with `open scoped BigOperators`, `open Matrix Module`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport`, `open LayoutScaledMatrices`):
--
--   ```lean
--   theorem centered_rationalDefect_rank_relative
--       (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (ε : ℚ)
--       (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
--       (hε : 0 < ε)
--       (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
--       (finrank ℚ (LinearMap.range (rationalDefect i t g
--         (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R).mulVecLin) : ℚ) ≤
--         ε * (Fintype.card (Joint t g i) : ℚ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Joint` and `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.rationalDefect` (definitions bundle `OAIQ081S055` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutNumeratorBridge.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative)

import Mathlib
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S055

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open Matrix Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport
open LayoutScaledMatrices

variable {r Q Δ : ℕ}

theorem centered_rationalDefect_rank_relative
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (R : ℕ) (ε : ℚ)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hε : 0 < ε)
    (hwidth : 32 * ((Q - 1 : ℕ) : ℝ) * Real.log (2 / (ε : ℝ)) ≤ (R : ℝ) ^ 2) :
    (finrank ℚ (LinearMap.range (rationalDefect i t g
      (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R).mulVecLin) : ℚ) ≤
      ε * (Fintype.card (Joint t g i) : ℚ) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end
