-- Prove2me | Theorems.Thm_OAI_MUB6_TaoCertificate_combined393_zero
-- name    : OAI.MUB6.TaoCertificate.combined393_zero
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-02T17:42:36.822106+00:00
-- url     : https://prove2.me/theorems/acfdf5b7-0e72-430a-94a2-2d946c94e782
-- title:
--   OAI.MUB6.TaoCertificate.combined393_zero: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.TaoCertificate.combined393_zero` of [lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge49.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge49.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6.TaoCertificate`, with `open TaoArithmetic`):
--
--   ```lean
--   theorem combined393_zero (f : Charge → ℂ)
--       (hcross : ∀ a c, Balanced a → Balanced c →
--         offDiagSum (fun i j => f (a + difference i j) *
--           star (g tao (c + difference i j))) = 0) :
--       Certificate.Integer.Sparse.eval combined393 (momentValues f) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.Balanced`, `OAI.MUB6.offDiagSum` and `OAI.MUB6.Certificate.Integer.Sparse.eval` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.difference` and `OAI.MUB6.TaoArithmetic.momentValues` (definitions bundle `OAIQ106D140` of this split); `OAI.MUB6.TaoCertificate.combined393` (definitions bundle `OAIQ106D188` of this split); `OAI.MUB6.Charge`, `OAI.MUB6.Coord`, `OAI.MUB6.g` and `OAI.MUB6.tao` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.TaoCertificate.combined431_zero` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/TaoCertificate/Merge49.lean (declaration OAI.MUB6.TaoCertificate.combined393_zero)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D188

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem combined393_zero (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0) :
    Certificate.Integer.Sparse.eval combined393 (momentValues f) = 0 := by
  sorry

end MUB6.TaoCertificate

end OAI
end
