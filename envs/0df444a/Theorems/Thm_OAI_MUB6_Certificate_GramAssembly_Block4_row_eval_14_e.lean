-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block4_row_eval_14_e
-- name    : OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-05T01:37:57.864751+00:00
-- url     : https://prove2.me/theorems/19a56082-0e0b-4415-b419-7ae8b9f217cc
-- title:
--   OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14` of [lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramAssembly.Block4`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem row_eval_14_e (x : Fin 2886 → ℝ) :
--       Integer.Sparse.eval node314 x =
--         ∑ j : Fin 22, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.GramAssembly.Block4.weights` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramAssembly.Block4.entries` (definitions bundle `OAIQ106E007` of this split); `OAI.MUB6.Certificate.GramAssembly.Block4.node314` (definitions bundle `OAIQ106E178` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramAssembly.Block4.rows_eval_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block4.lean (declaration OAI.MUB6.Certificate.GramAssembly.Block4.row_eval_14)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E178

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

open scoped BigOperators

theorem row_eval_14_e (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node314 x =
      ∑ j : Fin 22, (weights 14 j : ℝ) * Integer.Sparse.eval (entries 14 j) x := by
  sorry

end MUB6.Certificate.GramAssembly.Block4

end OAI
end
