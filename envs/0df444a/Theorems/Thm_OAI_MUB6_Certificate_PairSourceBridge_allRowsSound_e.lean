-- Prove2me | Theorems.Thm_OAI_MUB6_Certificate_PairSourceBridge_allRowsSound_e
-- name    : OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-06T06:04:50.875194+00:00
-- url     : https://prove2.me/theorems/b4c80314-1a1a-4871-a167-0b30df96a769
-- title:
--   OAI.MUB6.Certificate.PairSourceBridge.allRowsSound_e: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.Certificate.PairSourceBridge.allRowsSound` of [lean/OAI/Analysis/MutuallyUnbiased/PairSources/Main.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSources/Main.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.Certificate.PairSourceBridge`):
--
--   ```lean
--   theorem allRowsSound_e {H : CMatrix} (hH : IsHadamard H) (k : Fin 255) :
--       Integer.Sparse.eval (PairData.rows k) (momentVector H) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106E000` of this split); `OAI.MUB6.Certificate.PairData.rows` (definitions bundle `OAIQ106E140` of this split); `OAI.MUB6.Certificate.PairSourceBridge.momentVector` (definitions bundle `OAIQ106E149` of this split); `OAI.MUB6.CMatrix` and `OAI.MUB6.IsHadamard` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proofs of `OAI.MUB6.Certificate.PairSourceBridge.targetZero0_e`, `OAI.MUB6.family_size_le_five_e` and `OAI.MUB6.fourier_and_family_bound` of this split import it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/PairSources/Main.lean (declaration OAI.MUB6.Certificate.PairSourceBridge.allRowsSound)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E140
import Definitions.Def_OAIQ106E149

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.PairSourceBridge

theorem allRowsSound_e {H : CMatrix} (hH : IsHadamard H) (k : Fin 255) :
    Integer.Sparse.eval (PairData.rows k) (momentVector H) = 0 := by
  sorry

end MUB6.Certificate.PairSourceBridge

end OAI
end
