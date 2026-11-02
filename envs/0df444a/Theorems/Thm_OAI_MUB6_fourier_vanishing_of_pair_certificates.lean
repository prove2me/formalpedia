-- Prove2me | Theorems.Thm_OAI_MUB6_fourier_vanishing_of_pair_certificates
-- name    : OAI.MUB6.fourier_vanishing_of_pair_certificates
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:47:31.967438+00:00
-- url     : https://prove2.me/theorems/ab0bb886-cca2-40e4-a71c-f477f4f7cc61
-- title:
--   OAI.MUB6.fourier_vanishing_of_pair_certificates: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.fourier_vanishing_of_pair_certificates` of [lean/OAI/Analysis/MutuallyUnbiased/Fourier/FourierEndpoint.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Fourier/FourierEndpoint.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6`):
--
--   ```lean
--   theorem fourier_vanishing_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
--       (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame)
--       (hTao : ¬Equivalent H tao) (π : Equiv.Perm Coord) :
--       g H (permuteCharge π alpha) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.PairCertificateIdentity`, `OAI.MUB6.qCross` and `OAI.MUB6.qSame` (definitions bundle `OAIQ106D140` of this split); `OAI.MUB6.CMatrix`, `OAI.MUB6.Coord`, `OAI.MUB6.Equivalent`, `OAI.MUB6.IsHadamard`, `OAI.MUB6.alpha`, `OAI.MUB6.g`, `OAI.MUB6.permuteCharge` and `OAI.MUB6.tao` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.fourier_and_family_bound` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Fourier/FourierEndpoint.lean (declaration OAI.MUB6.fourier_vanishing_of_pair_certificates)

import Mathlib
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D140

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MUB6

theorem fourier_vanishing_of_pair_certificates {H : CMatrix} (hH : IsHadamard H)
    (hcross : PairCertificateIdentity H qCross) (hsame : PairCertificateIdentity H qSame)
    (hTao : ¬Equivalent H tao) (π : Equiv.Perm Coord) :
    g H (permuteCharge π alpha) = 0 := by
  sorry

end MUB6

end

end OAI
end
