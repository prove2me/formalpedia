-- Prove2me | Theorems.Thm_OAI_SymmetricMahler_equality_polar_gauge_medians_eq
-- name    : OAI.SymmetricMahler.equality_polar_gauge_medians_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:22:59.481988+00:00
-- url     : https://prove2.me/theorems/8600db16-9a89-4c61-b846-d0fc53f226b9
-- title:
--   OAI.SymmetricMahler.equality_polar_gauge_medians_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SymmetricMahler.equality_polar_gauge_medians` of [lean/OAI/Analysis/Mahler/Mahler/EqualityMedians.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/EqualityMedians.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SymmetricMahler`, with `open Set Filter Finset Metric`, `open scoped Topology`, `open Set Filter Finset Metric Complex`, `open scoped Topology`, `open MahlerConformal`, `open Set Filter Finset Metric Complex MeasureTheory`, `open scoped Topology`, `open MahlerConformal`, `open Set Finset MeasureTheory`, `open MahlerConformal`, `open Set MeasureTheory Metric`):
--
--   ```lean
--   theorem equality_polar_gauge_medians_eq {n : ℕ} (hn : 1 ≤ n)
--       {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
--       (hs : ∀ x ∈ K, -x ∈ K) (hi : (interior K).Nonempty)
--       (heq : (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n/Nat.factorial n) :
--       ∃ g h : RealNormData (Fin n → ℝ), g.unit = K ∧ h.unit = coordinatePolar K ∧
--         g.IsDual h ∧ HasMetricMedians h.Space ∧ HasMetricMedians g.Space
--   ```
--
--   **Definitions.** The statement is written with `OAI.SymmetricMahler.HasMetricMedians`, `OAI.SymmetricMahler.RealNormData`, `OAI.SymmetricMahler.RealNormData.IsDual`, `OAI.SymmetricMahler.RealNormData.Space`, `OAI.SymmetricMahler.RealNormData.unit` and `OAI.SymmetricMahler.RealNormData.Space.instNormedAddCommGroup` (definitions bundle `OAIQ2Ma000` of this split); `OAI.SymmetricMahler.coordinatePolar` (the published bundle `Def_SymmetricMahlerEquality`).
--
--   **Used by.** The proof of `OAI.SymmetricMahler.symmetric_mahler_equality` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/EqualityMedians.lean (declaration OAI.SymmetricMahler.equality_polar_gauge_medians)

import Mathlib
import Definitions.Def_SymmetricMahlerEquality
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

open Set Filter Finset Metric Complex MeasureTheory
open scoped Topology
open MahlerConformal

open Set Finset MeasureTheory
open MahlerConformal

open Set MeasureTheory Metric

theorem equality_polar_gauge_medians_eq {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K)
    (hs : ∀ x ∈ K, -x ∈ K) (hi : (interior K).Nonempty)
    (heq : (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n/Nat.factorial n) :
    ∃ g h : RealNormData (Fin n → ℝ), g.unit = K ∧ h.unit = coordinatePolar K ∧
      g.IsDual h ∧ HasMetricMedians h.Space ∧ HasMetricMedians g.Space := by
  sorry

end SymmetricMahler

end

end OAI
end
