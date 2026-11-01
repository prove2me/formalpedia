-- Prove2me | Theorems.Thm_OAI_Laughlin_Fock_weightedFourEnd_readout_s50
-- name    : OAI.Laughlin.Fock.weightedFourEnd_readout_s50
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-31T18:45:17.219885+00:00
-- url     : https://prove2.me/theorems/ec35e1af-6ed4-4220-a804-c050c61ae0b5
-- title:
--   OAI.Laughlin.Fock.weightedFourEnd_readout_s50: intermediate lemma from OpenAI, A Fock-space inequality and the Laughlin spectral gap
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Laughlin.planar_gap`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fock-space inequality and the Laughlin spectral gap*, OpenAI Math Release, September 24, 2026, result family 269, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Laughlin.Fock.weightedFourEnd_readout` of [lean/OAI/Analysis/Laughlin/FourBody/WeightedReadout.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/WeightedReadout.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Laughlin.Fock`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem weightedFourEnd_readout_s50 (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
--       (hS : ∀ j k, S k j = -S j k) (a b c d : Fin (Q+1)) :
--       weightedFourEnd Q p S (create a (create b (create c (create d (1 : Space Q))))) =
--         ((Real.sqrt 2*pairLimitCoefficient p a.val b.val*S c d -
--           Real.sqrt 2*pairLimitCoefficient p a.val c.val*S b d +
--           Real.sqrt 2*pairLimitCoefficient p a.val d.val*S b c +
--           Real.sqrt 2*pairLimitCoefficient p b.val c.val*S a d -
--           Real.sqrt 2*pairLimitCoefficient p b.val d.val*S a c +
--           Real.sqrt 2*pairLimitCoefficient p c.val d.val*S a b : ℝ) : ℂ) • (1 : Space Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Laughlin.Fock.create` (definitions bundle `OAIQ050L006` of this split); `OAI.Laughlin.Fock.weightedFourEnd` (definitions bundle `OAIQ050L007` of this split); `OAI.Laughlin.pairLimitCoefficient`, `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (the published bundle `Def_LaughlinPlanar`).
--
--   **Used by.** The proof of `OAI.Laughlin.Fock.limitFourColumn_physical_L_s50` of this split imports it.
-- source:
--   OpenAI, A Fock-space inequality and the Laughlin spectral gap, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 269; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Laughlin/FourBody/WeightedReadout.lean (declaration OAI.Laughlin.Fock.weightedFourEnd_readout)

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

theorem weightedFourEnd_readout_s50 (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b c d : Fin (Q+1)) :
    weightedFourEnd Q p S (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val*S c d -
        Real.sqrt 2*pairLimitCoefficient p a.val c.val*S b d +
        Real.sqrt 2*pairLimitCoefficient p a.val d.val*S b c +
        Real.sqrt 2*pairLimitCoefficient p b.val c.val*S a d -
        Real.sqrt 2*pairLimitCoefficient p b.val d.val*S a c +
        Real.sqrt 2*pairLimitCoefficient p c.val d.val*S a b : ℝ) : ℂ) • (1 : Space Q) := by
  sorry

end Laughlin.Fock

end OAI
end
