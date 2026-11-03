-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_row_eval_15
-- name    : OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:46:45.372024+00:00
-- url     : https://prove2.me/theorems/72cbabef-7679-4593-844a-eabc91bb6cf0
-- title:
--   OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15` of [lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramAssembly.Block1`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem row_eval_15 (x : Fin 2886 → ℝ) :
--       Integer.Sparse.eval node319 x =
--         ∑ j : Fin 21, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.GramAssembly.Block1.entries` and `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.Certificate.GramAssembly.Block1.weights` (definitions bundle `OAIQ106D001` of this split); `OAI.MUB6.Certificate.GramAssembly.Block1.node319` (definitions bundle `OAIQ106D069` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block1.lean (declaration OAI.MUB6.Certificate.GramAssembly.Block1.row_eval_15)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D001
import Definitions.Def_OAIQ106D069

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

theorem row_eval_15 (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node319 x =
      ∑ j : Fin 21, (weights 15 j : ℝ) * Integer.Sparse.eval (entries 15 j) x := by
  sorry

end MUB6.Certificate.GramAssembly.Block1

end OAI
end
