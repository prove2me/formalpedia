-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceFockHamiltonian_normal_square
-- name    : OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:32:33.41921+00:00
-- url     : https://prove2.me/theorems/a573376d-2459-49b0-bad2-5584318ee04f
-- title:
--   OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square: intermediate lemma from OpenAI, Uniform stability of the spherical Laughlin gap (result family 269)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Uniform stability of the spherical Laughlin gap (result family 269)*, OpenAI Math Release, October 5, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square` of [lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem sourceFockHamiltonian_normal_square (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
--       occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
--         (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
--         ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
--           occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.Orbital`, `OAI.Laughlin.Fock.Space`, `OAI.Laughlin.Fock.complexThreeGram`, `OAI.Laughlin.Fock.contractionForm`, `OAI.Laughlin.Spin.Orbital` and `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ047L000` of this split); `OAI.Laughlin.Fock.occupationNormSq`, `OAI.Laughlin.Fock.sourceFockEnergy`, `OAI.Laughlin.Fock.sourceFockHamiltonian`, `OAI.Laughlin.Fock.sourcePairEnd` and `OAI.Laughlin.Fock.sourceThreeEnd` (definitions bundle `OAIQ047L002` of this split).
--
--   **Used by.** The proofs of `OAI.Laughlin.Fock.physical_fock_kernel_distance_uniform` and `OAI_Laughlin_Fock_physical_fock_square_uniform` of this split import it.
-- source:
--   OpenAI, Uniform stability of the spherical Laughlin gap (result family 269), OpenAI Math Release, October 5, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Uniform-Stability-of-the-Spherical-Laughlin-Gap-October-5-2026/uniform-stability-spherical-laughlin-gap.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean (declaration OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square)

import Mathlib
import Definitions.Def_OAIQ047L002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem sourceFockHamiltonian_normal_square (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  sorry

end Laughlin.Fock

end OAI
end
