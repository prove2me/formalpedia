-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_problem_computed_energies
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:22.294518+00:00
-- url     : https://prove2.me/theorems/13ef2e0d-9035-4100-bb2f-1327a21aabe0
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsScope.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsScope.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes PackingProgram`, `open PackingProgram.Assembly`):
--
--   ```lean
--   theorem problem_computed_energies (p : PackingCallerProgram.Problem)
--       (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
--       (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
--       (hB : ∀ v,(Finset.univ.filter fun i =>
--         PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
--       (hb : ∀ e,(Finset.univ.filter fun i =>
--         PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
--       (hM : 0 < p.incidences) (hn : 0 < p.n)
--       (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
--       (hhead : 16*p.Q*p.r^2 ≤ p.n) :
--       Packing.energy (Packing.incidenceType
--         (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
--         (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
--         (problemAssignment p a tail)) ≤ (problemX p)^2 ∧
--       Packing.headEnergy (problemAssignment p a tail) ≤ ((p.n:ℚ)/(2*(p.r:ℚ)))^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.energy` (definitions bundle `OAIQ081S018` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeUniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.Incidences`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.factorCount` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.nativeEntries` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceType` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.factor` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics.owner` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.incidences` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headEnergy` (definitions bundle `OAIQ081S078` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problemAssignment` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problemX` (definitions bundle `OAIQ081S089` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.packing_coverage` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeadsScope.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies)

import Mathlib
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S089

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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

theorem problem_computed_energies (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) :
    Packing.energy (Packing.incidenceType
      (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
      (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
      (problemAssignment p a tail)) ≤ (problemX p)^2 ∧
    Packing.headEnergy (problemAssignment p a tail) ≤ ((p.n:ℚ)/(2*(p.r:ℚ)))^2 := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end
