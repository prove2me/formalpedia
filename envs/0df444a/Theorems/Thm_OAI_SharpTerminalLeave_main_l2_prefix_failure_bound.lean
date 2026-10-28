-- Prove2me | Theorems.Thm_OAI_SharpTerminalLeave_main_l2_prefix_failure_bound
-- name    : OAI.SharpTerminalLeave.main_l2_prefix_failure_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T06:53:05.809425+00:00
-- url     : https://prove2.me/theorems/3766f369-47de-4d06-b07c-120877baaa71
-- title:
--   OAI.SharpTerminalLeave.main_l2_prefix_failure_bound: intermediate lemma from OpenAI, The sharp terminal leave in random triangle removal
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpTerminalLeave.sharp_terminal_leave`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp terminal leave in random triangle removal*, OpenAI Math Release, September 25, 2026, result family 188, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpTerminalLeave.main_l2_prefix_failure_bound` of [lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/EvolveBindFinish.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/EvolveBindFinish.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpTerminalLeave`, with `open scoped BigOperators Topology Matrix.Norms.Operator`, `open MeasureTheory`, `open scoped BigOperators`, `open scoped BigOperators ENNReal Classical`, `open Filter MeasureTheory`, `open Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem main_l2_prefix_failure_bound (c C : ℝ) (hc : 0 < c) :
--       ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
--         expectation n (fun H => (normalizedLeave n H-sharpConstant)^2) ≤
--           δ+(2*(n : ℝ)+1)*prefixFailure n c C
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpTerminalLeave.prefixFailure` (definitions bundle `OAIQ4Tr000` of this split); `OAI.SharpTerminalLeave.Graph`, `OAI.SharpTerminalLeave.expectation`, `OAI.SharpTerminalLeave.normalizedLeave` and `OAI.SharpTerminalLeave.sharpConstant` (the published bundle `Def_TriangleRemoval`).
--
--   **Used by.** The proof of `OAI.SharpTerminalLeave.sharp_terminal_leave` of this split imports it.
-- source:
--   OpenAI, The sharp terminal leave in random triangle removal, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 188; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026/The-Sharp-Terminal-Leave-in-Random-Triangle-Removal-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/TriangleRemoval/TriangleRemoval/Process/EvolveBindFinish.lean (declaration OAI.SharpTerminalLeave.main_l2_prefix_failure_bound)

import Mathlib
import Definitions.Def_TriangleRemoval
import Definitions.Def_OAIQ4Tr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem main_l2_prefix_failure_bound (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      expectation n (fun H => (normalizedLeave n H-sharpConstant)^2) ≤
        δ+(2*(n : ℝ)+1)*prefixFailure n c C := by
  sorry

end SharpTerminalLeave

end

end OAI
end
