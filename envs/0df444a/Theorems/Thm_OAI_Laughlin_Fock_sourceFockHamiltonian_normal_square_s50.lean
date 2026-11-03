-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_sourceFockHamiltonian_normal_square_s50
-- name    : OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:53:55.227075+00:00
-- url     : https://prove2.me/theorems/98e849ae-f4ce-49ed-a568-1d704dc8e7f5
-- title:
--   OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square` of [lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators Matrix`):
--
--   ```lean
--   theorem sourceFockHamiltonian_normal_square_s50 (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
--       occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
--         (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
--         ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
--           occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Spin.Orbital` (definitions bundle `OAIQ050L003` of this split); `OAI.Laughlin.Fock.contractionForm` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.occupationNormSq` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.Fock.complexThreeGram` and `OAI.Laughlin.Spin.PairOrbitalIndex` (definitions bundle `OAIQ050L011` of this split); `OAI.Laughlin.Fock.sourceFockEnergy`, `OAI.Laughlin.Fock.sourceFockHamiltonian` and `OAI.Laughlin.Fock.sourcePairEnd` (definitions bundle `OAIQ050L012` of this split); `OAI.Laughlin.Fock.sourceThreeEnd` (definitions bundle `OAIQ050L017` of this split); `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.physical_fock_sharp_budget_eventually_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/Fock/NormalSquare.lean (declaration OAI.Laughlin.Fock.sourceFockHamiltonian_normal_square)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L017

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators Matrix

theorem sourceFockHamiltonian_normal_square_s50 (Q : ℕ) (hQ : 2 ≤ Q) (x : Space Q) :
    occupationNormSq Q (sourceFockHamiltonian Q x) = sourceFockEnergy Q x +
      (contractionForm Q (sourceThreeEnd Q) (complexThreeGram Q-1) x).re +
      ∑ p : Fin (2*Q-2+1), ∑ q : Fin (2*Q-2+1),
        occupationNormSq Q (sourcePairEnd Q q.val (sourcePairEnd Q p.val x)) := by
  sorry

end Laughlin.Fock

end OAI
end
