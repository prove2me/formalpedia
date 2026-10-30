-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_problem_head_max_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:49.199557+00:00
-- url     : https://prove2.me/theorems/5f5f3cfb-b178-4d4b-8f42-a44f80bef75f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsScope.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsScope.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes PackingProgram`, `open PackingProgram.Assembly`):
--
--   ```lean
--   theorem problem_head_max_bound (p : PackingCallerProgram.Problem)
--       (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
--       (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
--       (hB : ∀ v,(Finset.univ.filter fun i =>
--         PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
--       (hb : ∀ e,(Finset.univ.filter fun i =>
--         PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
--       (hM : 0 < p.incidences) (hn : 0 < p.n)
--       (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
--       (hhead : 16*p.Q*p.r^2 ≤ p.n) (low : Fin p.n → Bool) :
--       (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
--         (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.lowBits` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan.encodeWord` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.maxSelected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.Incidences`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.factorCount` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.nativeEntries` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.factor` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.owner` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.incidences` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.words` (definitions bundle `OAIQ081S089` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsScope.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound)

import Mathlib
import Definitions.Def_OAIQ081S089

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes PackingProgram
open PackingProgram.Assembly

theorem problem_head_max_bound (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) (low : Fin p.n → Bool) :
    (maxSelected p.n p.Q p.r ((p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
      (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(p.n:ℚ)/(2*(p.r:ℚ)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end
