-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval18504_e
-- name    : OAI.MUB6.Certificate.GramRows.rowEval18504_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:00:53.800844+00:00
-- url     : https://prove2.me/theorems/a7276451-cd23-4016-9b52-bae09008a9ca
-- title:
--   OAI.MUB6.Certificate.GramRows.rowEval18504_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramRows.rowEval18504` of [lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramRows`, with `open GramNormalization`):
--
--   ```lean
--   theorem rowEval18504_e (x : Key → ℝ) : Integer.Sparse.eval row18504 x =
--       Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramFunctions.Block5.form0` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.Certificate.GramRows.row18504` (definitions bundle `OAIQ106E039` of this split); `OAI.MUB6.Certificate.GramPolynomial.normalizedRow` (definitions bundle `OAIQ106E044` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.GramEntries.Block5.rowsSound2_0_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block168.lean (declaration OAI.MUB6.Certificate.GramRows.rowEval18504)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E039
import Definitions.Def_OAIQ106E044

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval18504_e (x : Key → ℝ) : Integer.Sparse.eval row18504 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 2, -1, 0, -2] GramFunctions.Block5.form0) x := by
  sorry

end MUB6.Certificate.GramRows

end OAI
end
