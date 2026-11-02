-- Prove2me | Theorems.Thm_OAI_MUB6_complete_family_not_equivalent_tao
-- name    : OAI.MUB6.complete_family_not_equivalent_tao
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T16:46:05.527849+00:00
-- url     : https://prove2.me/theorems/2f385913-06df-4f41-a2c6-1a9eedae4860
-- title:
--   OAI.MUB6.complete_family_not_equivalent_tao: intermediate lemma from OpenAI, The maximum number of mutually unbiased bases in dimension six
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MUB6.fourier_and_family_bound`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The maximum number of mutually unbiased bases in dimension six*, OpenAI Math Release, September 24, 2026, result family 266, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MUB6.complete_family_not_equivalent_tao` of [lean/OAI/Analysis/MutuallyUnbiased/Tao/TaoCompleteFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Tao/TaoCompleteFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MUB6`, with `open scoped BigOperators ComplexConjugate`):
--
--   ```lean
--   theorem complete_family_not_equivalent_tao (B : Fin 7 → Basis) (hB : IsMUBFamily B)
--       (r : Fin 7) (s : Coord) : ¬Equivalent (relativeMatrix B r s) tao
--   ```
--
--   **Definitions.** The statement is written with `OAI.MUB6.relativeMatrix` (definitions bundle `OAIQ106D000` of this split); `OAI.MUB6.Basis`, `OAI.MUB6.Coord`, `OAI.MUB6.Equivalent`, `OAI.MUB6.IsMUBFamily` and `OAI.MUB6.tao` (the published bundle `Def_MUBSix`).
--
--   **Used by.** The proof of `OAI.MUB6.complete_family_fourier_zero` of this split imports it.
-- source:
--   OpenAI, The maximum number of mutually unbiased bases in dimension six, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 266; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026/The-maximum-number-of-mutually-unbiased-bases-in-dimension-six-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/MutuallyUnbiased/Tao/TaoCompleteFamily.lean (declaration OAI.MUB6.complete_family_not_equivalent_tao)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

theorem complete_family_not_equivalent_tao (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (r : Fin 7) (s : Coord) : ¬Equivalent (relativeMatrix B r s) tao := by
  sorry

end MUB6

end

end OAI
end
