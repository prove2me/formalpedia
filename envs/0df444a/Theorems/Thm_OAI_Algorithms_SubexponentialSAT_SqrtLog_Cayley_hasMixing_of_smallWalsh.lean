-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Cayley_hasMixing_of_smallWalsh
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:36:26.812978+00:00
-- url     : https://prove2.me/theorems/d521f168-bd77-4e5b-a6e4-e4c8f6aa8b47
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CayleyGraph.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CayleyGraph.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley`, with `open scoped BigOperators`, `open SubexponentialSAT.SqrtLog.SparseCode`):
--
--   ```lean
--   theorem hasMixing_of_smallWalsh (shifts : P → Cube r) (ε : ℝ)
--       (hε : 0 ≤ ε) (hW : SmallWalsh shifts ε) : (graph shifts).HasMixing ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.Cube`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.SmallWalsh` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.graph` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.PortGraph.HasMixing` (definitions bundle `OAIQ081S042` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.supplied_kernel_bound_of_coverage` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/CayleyGraph.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Cayley.hasMixing_of_smallWalsh)

import Mathlib
import Definitions.Def_OAIQ081S042

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistence.instDecidableGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators
open SubexponentialSAT.SqrtLog.SparseCode

variable {r : ℕ} {P : Type*}

variable [Fintype P]

theorem hasMixing_of_smallWalsh (shifts : P → Cube r) (ε : ℝ)
    (hε : 0 ≤ ε) (hW : SmallWalsh shifts ε) : (graph shifts).HasMixing ε := by
  sorry

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
end
