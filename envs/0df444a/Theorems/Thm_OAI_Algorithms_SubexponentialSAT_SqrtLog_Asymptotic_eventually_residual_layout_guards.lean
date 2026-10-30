-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Asymptotic_eventually_residual_layout_guards
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:15:27.917+00:00
-- url     : https://prove2.me/theorems/6dfeb04f-0bff-433f-9d57-43c7611403b2
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/AsymptoticResidualLayout.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/AsymptoticResidualLayout.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic`, with `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem eventually_residual_layout_guards (q : ℕ) :
--       ∀ᶠ n : ℕ in atTop, ∀ m a b : ℕ, n ≤ 2 * m → a ≤ L m ^ q → b ≤ L m ^ q →
--         2 ≤ layoutQ m ∧
--         4 * layoutCutoff m b ≤ layoutQ m ∧
--         16 * layoutQ m * layoutR m ^ 2 ≤ m ∧
--         4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
--           (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤ m
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.layoutCutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.layoutQ` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.layoutR` (definitions bundle `OAIQ081S003` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.eventually_measured_guards` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/AsymptoticResidualLayout.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.eventually_residual_layout_guards)

import Mathlib
import Definitions.Def_OAIQ081S003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Asymptotic

open Filter
open scoped Topology

theorem eventually_residual_layout_guards (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m a b : ℕ, n ≤ 2 * m → a ≤ L m ^ q → b ≤ L m ^ q →
      2 ≤ layoutQ m ∧
      4 * layoutCutoff m b ≤ layoutQ m ∧
      16 * layoutQ m * layoutR m ^ 2 ≤ m ∧
      4096 * (b + a) * b ^ 2 * layoutR m ^ 2 * L m ^ 4 *
        (layoutR m ^ (2 * layoutQ m)) ^ 2 ≤ m := by
  sorry

end SubexponentialSAT.SqrtLog.Asymptotic

end OAI.Algorithms
end
