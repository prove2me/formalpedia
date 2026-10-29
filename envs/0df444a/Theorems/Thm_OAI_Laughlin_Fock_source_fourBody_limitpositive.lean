-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_source_fourBody_limitpositive
-- name    : OAI.Laughlin.Fock.source_fourBody_limitpositive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:33:11.318019+00:00
-- url     : https://prove2.me/theorems/e360bbeb-daff-4d87-9322-b3f47d8bee1c
-- title:
--   OAI.Laughlin.Fock.source_fourBody_limitpositive: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.source_fourBody_limitpositive` of [lean/OAI/Analysis/Laughlin/FourBody/LimitPositive.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/LimitPositive.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped Matrix BigOperators ComplexOrder`, `open Matrix Spin`):
--
--   ```lean
--   theorem source_fourBody_limitpositive (Q D : ℕ) (hQ : D+1 ≤ Q)
--       (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
--       0 ≤ (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2), physicalLimitMiddle D i j *
--         occupationInner Q (limitFourCopyEnd Q (Certificate.copyLabel i) D x)
--           (limitFourCopyEnd Q (Certificate.copyLabel j) D x)).re
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Certificate.copyLabel`, `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space` and `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.limitFourCopyEnd` and `OAI.Laughlin.Fock.physicalLimitMiddle` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_fourBody_total_haar_transfer` and `OAI_Laughlin_Fock_source_fourBody_uniform_transfer` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/LimitPositive.lean (declaration OAI.Laughlin.Fock.source_fourBody_limitpositive)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

theorem source_fourBody_limitpositive (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    0 ≤ (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2), physicalLimitMiddle D i j *
      occupationInner Q (limitFourCopyEnd Q (Certificate.copyLabel i) D x)
        (limitFourCopyEnd Q (Certificate.copyLabel j) D x)).re := by
  sorry

end Laughlin.Fock

end OAI
end
