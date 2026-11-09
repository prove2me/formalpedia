-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_MixedData_mergedZero1813_e
-- name    : OAI.MUB6.Certificate.MixedData.mergedZero1813_e
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-07T20:44:52.416751+00:00
-- url     : https://prove2.me/theorems/3b5b1f5e-f48a-480e-ba4c-fcceb5d2f551
-- title:
--   OAI.MUB6.Certificate.MixedData.mergedZero1813_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.MixedData.mergedZero1813` of [lean/OAI/Analysis/MutuallyUnbiased/MixedMerge/Block56.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMerge/Block56.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.MixedData`):
--
--   ```lean
--   theorem mergedZero1813_e (x : Fin 3237 → ℝ)
--       (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1813 x = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.MixedData.merged1813` (definitions bundle `OAIQ106E061` of this split); `OAI.MUB6.Certificate.MixedData.sourceRows` (definitions bundle `OAIQ106E077` of this split).
--
--   **Used by.** The proof of `OAI.MUB6.Certificate.MixedData.mergedZero1814_e` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/MixedMerge/Block56.lean (declaration OAI.MUB6.Certificate.MixedData.mergedZero1813)

import Mathlib
import Definitions.Def_OAIQ106E061
import Definitions.Def_OAIQ106E077

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.MixedData

theorem mergedZero1813_e (x : Fin 3237 → ℝ)
    (h : ∀ k, Integer.Sparse.eval (sourceRows k) x = 0) : Integer.Sparse.eval merged1813 x = 0 := by
  sorry

end MUB6.Certificate.MixedData

end OAI
end
