-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block1_rows_eval_e
-- name    : OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-06T06:04:37.541428+00:00
-- url     : https://prove2.me/theorems/a2ec1520-aa2a-4e37-bb25-d0308d1533a9
-- title:
--   OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval` of [lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramAssembly.Block1`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem rows_eval_e (i : Fin 21) (x : Fin 2886 → ℝ) :
--       Integer.Sparse.eval (rows i) x =
--         ∑ j : Fin 21, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.GramAssembly.Block1.entries` and `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.GramAssembly.Block1.rows` (definitions bundle `OAIQ106E001` of this split); `OAI.MUB6.Certificate.GramAssembly.Block1.weights` (definitions bundle `OAIQ106E002` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramAssembly.Block1.polynomial_eval_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramAssembly/Block1.lean (declaration OAI.MUB6.Certificate.GramAssembly.Block1.rows_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E001
import Definitions.Def_OAIQ106E002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

open scoped BigOperators

theorem rows_eval_e (i : Fin 21) (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval (rows i) x =
      ∑ j : Fin 21, (weights i j : ℝ) * Integer.Sparse.eval (entries i j) x := by
  sorry

end MUB6.Certificate.GramAssembly.Block1

end OAI
end
