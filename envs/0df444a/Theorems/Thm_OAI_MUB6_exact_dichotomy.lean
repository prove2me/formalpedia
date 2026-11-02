-- Prove2me | Theorems.Thm_OAI_MUB6_exact_dichotomy
-- name    : OAI.MUB6.exact_dichotomy
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:46:49.352361+00:00
-- url     : https://prove2.me/theorems/b7325087-543d-44aa-b4a9-8806589c002d
-- title:
--   OAI.MUB6.exact_dichotomy: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.exact_dichotomy` of [lean/OAI/Analysis/MutuallyUnbiased/Fourier/FourierTheorem.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Fourier/FourierTheorem.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6`):
--
--   ```lean
--   theorem exact_dichotomy {H : CMatrix} (hH : IsHadamard H) :
--       FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.FourierZero` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.CMatrix`, `OAI.MUB6.Coord` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.complete_family_fourier_zero` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Fourier/FourierTheorem.lean (declaration OAI.MUB6.exact_dichotomy)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem exact_dichotomy {H : CMatrix} (hH : IsHadamard H) :
    FourierZero H ∨ IsHadamard (fun i j => H i j ^ 2) := by
  sorry

end MUB6

end

end OAI
end
