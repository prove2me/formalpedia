-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CostAssembly_eventually_support_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:41:18.721289+00:00
-- url     : https://prove2.me/theorems/365ee9c0-71ff-4e4a-a632-177f34fefd90
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyUniform.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyUniform.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly`, with `open Filter`, `open scoped Topology`, `open Asymptotic`):
--
--   ```lean
--   theorem eventually_support_bound {C : ℝ} (hC : 1 ≤ C) :
--       ∀ᶠ n : ℕ in atTop, ∀ J : ℕ, (J : ℝ) ≤ entropyCutoff n C →
--         (SupportProgram.count n J : ℝ) ≤
--         (2 : ℝ)^((384 * C + 1) * Statement.runtimeScale n)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.SupportProgram.count` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.entropyCutoff` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeScale` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.assembledWork_uniform_cutoff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_nativeEnvelope_bound` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CostAssemblyUniform.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_support_bound)

import Mathlib
import Definitions.Def_SubexponentialSAT
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

theorem eventually_support_bound {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ n : ℕ in atTop, ∀ J : ℕ, (J : ℝ) ≤ entropyCutoff n C →
      (SupportProgram.count n J : ℝ) ≤
      (2 : ℝ)^((384 * C + 1) * Statement.runtimeScale n) := by
  sorry

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
end
