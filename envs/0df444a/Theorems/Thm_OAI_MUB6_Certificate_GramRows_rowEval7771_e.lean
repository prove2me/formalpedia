-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_GramRows_rowEval7771_e
-- name    : OAI.MUB6.Certificate.GramRows.rowEval7771_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T13:01:46.26507+00:00
-- url     : https://prove2.me/theorems/2c367466-b699-43c3-8ec0-ec55fa10b8ad
-- title:
--   OAI.MUB6.Certificate.GramRows.rowEval7771_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.GramRows.rowEval7771` of [lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block84.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block84.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.GramRows`, with `open GramNormalization`):
--
--   ```lean
--   theorem rowEval7771_e (x : Key → ℝ) : Integer.Sparse.eval row7771 x =
--       Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form5) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.GramNormalization.Key` (definitions bundle `OAIQ106E002` of this split); `OAI.MUB6.Certificate.GramFunctions.Block3.form5` (definitions bundle `OAIQ106E018` of this split); `OAI.MUB6.Certificate.GramRows.row7771` (definitions bundle `OAIQ106E029` of this split); `OAI.MUB6.Certificate.GramPolynomial.normalizedRow` (definitions bundle `OAIQ106E044` of this split).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.GramEntries.Block3.rowsSound5_5_e` and `OAI.MUB6.Certificate.GramEntries.Block3.rowsSound9_5_e` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/GramRows/Block84.lean (declaration OAI.MUB6.Certificate.GramRows.rowEval7771)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E018
import Definitions.Def_OAIQ106E029
import Definitions.Def_OAIQ106E044

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

theorem rowEval7771_e (x : Key → ℝ) : Integer.Sparse.eval row7771 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -2, 2, 0, -1] GramFunctions.Block3.form5) x := by
  sorry

end MUB6.Certificate.GramRows

end OAI
end
