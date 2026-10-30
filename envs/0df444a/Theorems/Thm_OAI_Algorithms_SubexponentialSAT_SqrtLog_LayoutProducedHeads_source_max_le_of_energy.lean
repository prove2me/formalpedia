-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedHeads_source_max_le_of_energy
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:47.505081+00:00
-- url     : https://prove2.me/theorems/ab566f3e-2ca1-4d2d-9876-adeae001516e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeads.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeads.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes LeafHeadSetupProgram`):
--
--   ```lean
--   theorem source_max_le_of_energy
--       (owner : I → Fin n) (factor : I → Fin N)
--       (a : Word r Q) (tail : List (Word r Q))
--       (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
--       (x : ℚ) (hr : 0 < r)
--       (hy : ((n:ℚ)/(2*(r:ℚ)))^2=(w.incidence:ℚ)/w.denominator)
--       (hx : x^2=(w.head:ℚ)/w.denominator)
--       (low : Fin n → Bool)
--       (henergy : Packing.headEnergy (Packing.computedWords owner factor a tail terms
--         (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) ≤
--           ((n:ℚ)/(2*(r:ℚ)))^2) :
--       (maxSelected n Q r (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
--         (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(n:ℚ)/(2*(r:ℚ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.lowBits` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.ScoreTerm` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Weights` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.maxSelected` (definitions bundle `OAIQ081S035` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.indices` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.computedWords` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headEnergy` (definitions bundle `OAIQ081S078` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.sourceRows` (definitions bundle `OAIQ081S091` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedHeads.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.source_max_le_of_energy)

import Mathlib
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S091

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes LeafHeadSetupProgram

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

omit [DecidableEq I] in
theorem source_max_le_of_energy
    (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x : ℚ) (hr : 0 < r)
    (hy : ((n:ℚ)/(2*(r:ℚ)))^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator)
    (low : Fin n → Bool)
    (henergy : Packing.headEnergy (Packing.computedWords owner factor a tail terms
      (LeafHeadFactorsProgram.indices n N) x ((n:ℚ)/(2*(r:ℚ)))) ≤
        ((n:ℚ)/(2*(r:ℚ)))^2) :
    (maxSelected n Q r (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits low) : ℚ) ≤ 3*(n:ℚ)/(2*(r:ℚ)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end
