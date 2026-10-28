-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_stripMap_volume_le_product
-- name    : OAI.SymmetricMahler.stripMap_volume_le_product
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:59.164997+00:00
-- url     : https://prove2.me/theorems/f9201299-501c-40d1-b27b-71a64ab91208
-- title:
--   OAI.SymmetricMahler.stripMap_volume_le_product: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SymmetricMahler.stripMap_volume_le_product` of [lean/OAI/Analysis/Mahler/Mahler/StripVolume.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/StripVolume.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SymmetricMahler`, with `open Real Complex Set Finset MeasureTheory`, `open scoped Topology ENNReal Pointwise`, `open MahlerConformal`):
--
--   ```lean
--   theorem stripMap_volume_le_product (A : Matrix (Fin N) (Fin n) ℝ)
--       {m : ℕ} (hm : 2 ≤ m) :
--       volume (stripMap A m '' stripSublevel A m) ≤
--         volume (stripBody A) * (ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)*
--           volume (coordinatePolar (stripBody A)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SymmetricMahler.planarError`, `OAI.SymmetricMahler.stripBody`, `OAI.SymmetricMahler.stripMap` and `OAI.SymmetricMahler.stripSublevel` (definitions bundle `OAISMh000` of this split); `OAI.SymmetricMahler.coordinatePolar` (the published bundle `Def_MahlerConjecture`).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/StripVolume.lean (declaration OAI.SymmetricMahler.stripMap_volume_le_product)

import Mathlib
import Definitions.Def_MahlerConjecture
import Definitions.Def_OAISMh000

section

attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SymmetricMahler
open Real Complex Set Finset MeasureTheory
open scoped Topology ENNReal Pointwise
open MahlerConformal
variable {n N : ℕ}

theorem stripMap_volume_le_product (A : Matrix (Fin N) (Fin n) ℝ)
    {m : ℕ} (hm : 2 ≤ m) :
    volume (stripMap A m '' stripSublevel A m) ≤
      volume (stripBody A) * (ENNReal.ofReal ((1+(N : ℝ)*planarError m)^n)*
        volume (coordinatePolar (stripBody A))) := by
  sorry

end SymmetricMahler

end OAI
end
