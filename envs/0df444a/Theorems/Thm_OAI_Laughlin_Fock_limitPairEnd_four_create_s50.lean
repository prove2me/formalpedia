-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_limitPairEnd_four_create_s50
-- name    : OAI.Laughlin.Fock.limitPairEnd_four_create_s50
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:43:49.52447+00:00
-- url     : https://prove2.me/theorems/ca10f672-32b0-4a25-9dcd-b54cf62deb48
-- title:
--   OAI.Laughlin.Fock.limitPairEnd_four_create_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.limitPairEnd_four_create` of [lean/OAI/Analysis/Laughlin/FourBody/LimitCARReadout.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/LimitCARReadout.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem limitPairEnd_four_create_s50 (Q p : ℕ) (a b c d : Fin (Q+1)) :
--       limitPairEnd Q p (create a (create b (create c (create d (1 : Space Q))))) =
--         ((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) • create c (create d (1 : Space Q)) -
--         ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) • create b (create d (1 : Space Q)) +
--         ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) • create b (create c (1 : Space Q)) +
--         ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) • create a (create d (1 : Space Q)) -
--         ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) • create a (create c (1 : Space Q)) +
--         ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) • create a (create b (1 : Space Q))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.create` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.limitPairEnd` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.pairLimitCoefficient`, `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.weightedFourEnd_readout_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/LimitCARReadout.lean (declaration OAI.Laughlin.Fock.limitPairEnd_four_create)

import Mathlib
import Definitions.Def_LaughlinPlanar
import Definitions.Def_OAIQ050L006
import Definitions.Def_OAIQ050L007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem limitPairEnd_four_create_s50 (Q p : ℕ) (a b c d : Fin (Q+1)) :
    limitPairEnd Q p (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) • create c (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) • create b (create d (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) • create b (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) • create a (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) • create a (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) • create a (create b (1 : Space Q)) := by
  sorry

end Laughlin.Fock

end OAI
end
