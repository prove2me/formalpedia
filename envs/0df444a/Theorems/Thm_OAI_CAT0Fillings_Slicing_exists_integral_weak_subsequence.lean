-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_Slicing_exists_integral_weak_subsequence
-- name    : OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:41:18.668097+00:00
-- url     : https://prove2.me/theorems/9f230c73-005a-4c22-a906-6b9115661446
-- title:
--   OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence` of [lean/OAI/Geometry/CAT0Fillings/Fillings/Attainment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Fillings/Attainment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings.Slicing`, with `open Set Filter MeasureTheory Metric`, `open scoped Topology NNReal`):
--
--   ```lean
--   theorem exists_integral_weak_subsequence {k : ℕ} {Ts : ℕ → Functional X (k+1+1)}
--       (hTs : ∀ j, IsIntegral (k+1+1) (Ts j)) (M N : ℝ≥0)
--       (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
--       (hX : IsCAT0 X) :
--       ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧ ∃ T : Functional X (k+1+1),
--         IsIntegral (k+1+1) T ∧ mass T ≤ M ∧ mass (boundarySucc T) ≤ N ∧
--         ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.boundarySucc` and `OAI.CAT0Fillings.mass` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proofs of `OAI.CAT0Fillings.exists_filling_mass_eq`, `OAI.CAT0Fillings.fillingVolume_le_two` and `OAI.CAT0Fillings.sharp_integral_filling` of this split import it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Fillings/Attainment.lean (declaration OAI.CAT0Fillings.Slicing.exists_integral_weak_subsequence)

import Mathlib
import Definitions.Def_SharpCAT0Filling

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_integral_weak_subsequence {k : ℕ} {Ts : ℕ → Functional X (k+1+1)}
    (hTs : ∀ j, IsIntegral (k+1+1) (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundarySucc (Ts j)) ≤ N)
    (hX : IsCAT0 X) :
    ∃ (ψ : ℕ → ℕ), StrictMono ψ ∧ ∃ T : Functional X (k+1+1),
      IsIntegral (k+1+1) T ∧ mass T ≤ M ∧ mass (boundarySucc T) ≤ N ∧
      ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π)) := by
  sorry

end CAT0Fillings.Slicing
end

end OAI
end
