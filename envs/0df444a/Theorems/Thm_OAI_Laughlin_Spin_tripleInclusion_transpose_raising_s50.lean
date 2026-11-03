-- Prove2me | Theorems.Thm_OAI_Laughlin_Spin_tripleInclusion_transpose_raising_s50
-- name    : OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:57:48.099515+00:00
-- url     : https://prove2.me/theorems/3acb0b3f-94b0-4e86-b6f1-84d1927ed34d
-- title:
--   OAI.Laughlin.Spin.tripleInclusion_transpose_raising_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Spin.tripleInclusion_transpose_raising` of [lean/OAI/Analysis/Laughlin/Spin/TripleLadderIntertwining.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TripleLadderIntertwining.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Spin`, with `open scoped BigOperators Matrix Kronecker`):
--
--   ```lean
--   theorem tripleInclusion_transpose_raising_s50 (Q : ℕ) (hQ : 0 < Q) :
--       (tripleInclusion Q)ᵀ * tripleRaise Q = totalRaise (2*Q-2) Q * (tripleInclusion Q)ᵀ
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Spin.totalRaise` (definitions bundle `OAIQ050L010` of this split); `OAI.Laughlin.Spin.PairOrbitalIndex`, `OAI.Laughlin.Spin.TripleIndex` and `OAI.Laughlin.Spin.tripleInclusion` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Spin.tripleRaise` (definitions bundle `OAIQ050L019` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Spin.threeGram_raising_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Spin/TripleLadderIntertwining.lean (declaration OAI.Laughlin.Spin.tripleInclusion_transpose_raising)

import Mathlib
import Definitions.Def_OAIQ050L019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix Kronecker

theorem tripleInclusion_transpose_raising_s50 (Q : ℕ) (hQ : 0 < Q) :
    (tripleInclusion Q)ᵀ * tripleRaise Q = totalRaise (2*Q-2) Q * (tripleInclusion Q)ᵀ := by
  sorry

end Laughlin.Spin

end OAI
end
