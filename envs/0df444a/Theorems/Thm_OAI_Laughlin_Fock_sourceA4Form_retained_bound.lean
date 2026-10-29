-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceA4Form_retained_bound
-- name    : OAI.Laughlin.Fock.sourceA4Form_retained_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:32:17.696764+00:00
-- url     : https://prove2.me/theorems/ebd5adff-0fa0-43ed-a2e2-ed859bc948d1
-- title:
--   OAI.Laughlin.Fock.sourceA4Form_retained_bound: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceA4Form_retained_bound` of [lean/OAI/Analysis/Laughlin/FourBody/RetainedComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/RetainedComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open Spin Rotation MeasureTheory`, `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem sourceA4Form_retained_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
--       sourceA4Form Q x ≤ retainedFourTarget Q hQ x +
--         (10946*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.averagedFourTransferError` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.retainedFourTarget`, `OAI.Laughlin.Fock.sourceA4Form` and `OAI.Laughlin.Fock.sourceFockEnergy` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_fock_kernel_distance_uniform` and `OAI_Laughlin_Fock_sourceA4Form_bound` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/RetainedComparison.lean (declaration OAI.Laughlin.Fock.sourceA4Form_retained_bound)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open Spin Rotation MeasureTheory
open scoped BigOperators Matrix

theorem sourceA4Form_retained_bound (Q : ℕ) (hQ : 25 ≤ Q) (x : Space Q) :
    sourceA4Form Q x ≤ retainedFourTarget Q hQ x +
      (10946*(3/10^6 : ℝ)+averagedFourTransferError Q)*sourceFockEnergy Q x := by
  sorry

end Laughlin.Fock

end OAI
end
