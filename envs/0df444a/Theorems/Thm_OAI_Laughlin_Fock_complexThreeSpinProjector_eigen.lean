-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_complexThreeSpinProjector_eigen
-- name    : OAI.Laughlin.Fock.complexThreeSpinProjector_eigen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:28:47.121624+00:00
-- url     : https://prove2.me/theorems/5bc4e74e-687e-40f7-8459-770fbec8c9f3
-- title:
--   OAI.Laughlin.Fock.complexThreeSpinProjector_eigen: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.complexThreeSpinProjector_eigen` of [lean/OAI/Analysis/Laughlin/ThreeBody/NullSectors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/NullSectors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem complexThreeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
--       complexThreeGram Q * complexThreeSpinProjector Q hQ z =
--         ((1+gramEigenvalueFormula Q z.val : ℝ) : ℂ) • complexThreeSpinProjector Q hQ z
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.complexThreeGram`, `OAI.Laughlin.Fock.complexThreeSpinProjector`, `OAI.Laughlin.Spin.Orbital` and `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.gramEigenvalueFormula` (definitions bundle `OAIQ047L001` of this split).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_threeBody_Fock_comparison_eventually` of this split imports it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/ThreeBody/NullSectors.lean (declaration OAI.Laughlin.Fock.complexThreeSpinProjector_eigen)

import Mathlib
import Definitions.Def_OAIQ047L000
import Definitions.Def_OAIQ047L001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem complexThreeSpinProjector_eigen (Q : ℕ) (hQ : 2 ≤ Q) (z : Fin (Q+1)) :
    complexThreeGram Q * complexThreeSpinProjector Q hQ z =
      ((1+gramEigenvalueFormula Q z.val : ℝ) : ℂ) • complexThreeSpinProjector Q hQ z := by
  sorry

end Laughlin.Fock

end OAI
end
