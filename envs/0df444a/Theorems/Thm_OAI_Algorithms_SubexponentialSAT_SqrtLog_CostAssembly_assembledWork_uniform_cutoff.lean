-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_assembledWork_uniform_cutoff
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:36:43.499671+00:00
-- url     : https://prove2.me/theorems/5e39b0ba-ea30-4b8b-83ba-befc0d4da417
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyUniform.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyUniform.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly`, with `open Filter`, `open scoped Topology`, `open Asymptotic`):
--
--   ```lean
--   theorem assembledWork_uniform_cutoff (k qi ql d : ℕ) :
--       ∃N:ℕ, ∀n ≥ N, ∀p:Resources, Bounds qi ql d n p →
--         (assembledWork k n p:ℝ) ≤
--           17*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Resources` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.exponentConstant` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Bounds` (definitions bundle `OAIQ081S029` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeScale` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.runtime_bound` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyUniform.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly
open Filter
open scoped Topology
open Asymptotic

theorem assembledWork_uniform_cutoff (k qi ql d : ℕ) :
    ∃N:ℕ, ∀n ≥ N, ∀p:Resources, Bounds qi ql d n p →
      (assembledWork k n p:ℝ) ≤
        17*(2:ℝ)^(exponentConstant k ql*Statement.runtimeScale n) := by
  sorry

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end
