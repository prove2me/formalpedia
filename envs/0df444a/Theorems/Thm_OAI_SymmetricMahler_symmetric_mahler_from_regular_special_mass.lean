-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_symmetric_mahler_from_regular_special_mass
-- name    : OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:26.279302+00:00
-- url     : https://prove2.me/theorems/e4b11f73-87b0-4306-8d06-4944db418b4e
-- title:
--   OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass` of [lean/OAI/Analysis/Mahler/Mahler/RegularMassReduction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/RegularMassReduction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SymmetricMahler`, with `open Set MeasureTheory`):
--
--   ```lean
--   theorem symmetric_mahler_from_regular_special_mass {n : ℕ} (hn : 1 ≤ n)
--       (hmass : ∀ N (A : Matrix (Fin N) (Fin n) ℝ), Function.Injective (measurement A) →
--         ∀ m : ℕ, 2 ≤ m → ∀ k, SpecialRegularMassBound A m k)
--       {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
--       (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
--       (4 : ℝ)^n/(Nat.factorial n : ℝ) ≤
--         (volume K).toReal*(volume (coordinatePolar K)).toReal
--   ```
--
--   **Definitions.** The statement is written with `OAI.SymmetricMahler.SpecialRegularMassBound` and `OAI.SymmetricMahler.measurement` (definitions bundle `OAISMh000` of this split); `OAI.SymmetricMahler.coordinatePolar` (the published bundle `Def_MahlerConjecture`).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.symmetric_mahler` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/RegularMassReduction.lean (declaration OAI.SymmetricMahler.symmetric_mahler_from_regular_special_mass)

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
open Set MeasureTheory

theorem symmetric_mahler_from_regular_special_mass {n : ℕ} (hn : 1 ≤ n)
    (hmass : ∀ N (A : Matrix (Fin N) (Fin n) ℝ), Function.Injective (measurement A) →
      ∀ m : ℕ, 2 ≤ m → ∀ k, SpecialRegularMassBound A m k)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4 : ℝ)^n/(Nat.factorial n : ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  sorry

end SymmetricMahler

end OAI
end
