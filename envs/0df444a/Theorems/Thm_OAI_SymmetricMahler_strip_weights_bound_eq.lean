-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_strip_weights_bound_eq
-- name    : OAI.SymmetricMahler.strip_weights_bound_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:26:20.27439+00:00
-- url     : https://prove2.me/theorems/3806f8fb-1dbc-4907-8fd0-5e0c2f1c99f6
-- title:
--   OAI.SymmetricMahler.strip_weights_bound_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SymmetricMahler.strip_weights_bound` of [lean/OAI/Analysis/Mahler/Mahler/EqualityMedians.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/EqualityMedians.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SymmetricMahler`, with `open Set Filter Finset Metric`, `open scoped Topology`, `open Set Filter Finset Metric Complex`, `open scoped Topology`, `open MahlerConformal`):
--
--   ```lean
--   lemma strip_weights_bound_eq {n N m : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
--       (hm : 2 ≤ m) {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripSublevel A m) :
--       (∑ j, |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)|) ≤
--         1+(N:ℝ)*planarError m
--   ```
--
--   **Definitions.** The statement is written with `OAI.SymmetricMahler.measurement`, `OAI.SymmetricMahler.planarError`, `OAI.SymmetricMahler.planarPrimitive` and `OAI.SymmetricMahler.stripSublevel` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.equality_polar_gauge_medians_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/EqualityMedians.lean (declaration OAI.SymmetricMahler.strip_weights_bound)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Filter Finset Metric
open scoped Topology

open Set Filter Finset Metric Complex
open scoped Topology
open MahlerConformal

lemma strip_weights_bound_eq {n N m : ℕ} (A : Matrix (Fin N) (Fin n) ℝ)
    (hm : 2 ≤ m) {z : (Fin n → ℝ) × (Fin n → ℝ)} (hz : z ∈ stripSublevel A m) :
    (∑ j, |planarPrimitive m (measurement A z.1 j) (measurement A z.2 j)|) ≤
      1+(N:ℝ)*planarError m := by
  sorry

open Set Filter Finset Metric Complex MeasureTheory
open scoped Topology
open MahlerConformal

open Set Finset MeasureTheory
open MahlerConformal

open Set MeasureTheory Metric

end SymmetricMahler

end

end OAI
end
