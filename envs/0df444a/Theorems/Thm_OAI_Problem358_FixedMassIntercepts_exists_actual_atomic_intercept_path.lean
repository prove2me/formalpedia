-- Prove2me | Theorems.Thm_OAI_Problem358_FixedMassIntercepts_exists_actual_atomic_intercept_path
-- name    : OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T09:22:12.302267+00:00
-- url     : https://prove2.me/theorems/ec408405-d464-44e1-9acf-e6af59d44126
-- title:
--   OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path: intermediate lemma from OpenAI, Sharp One-Third Stability of Brenier Maps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem358.one_third_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp One-Third Stability of Brenier Maps*, OpenAI Math Release, September 25, 2026, result family 374, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path` of [lean/OAI/Analysis/Brenier/Brenier/CanonicalPaths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Brenier/Brenier/CanonicalPaths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem358.FixedMassIntercepts`, with `open Set MeasureTheory`, `open scoped BigOperators NNReal ContDiff`):
--
--   ```lean
--   theorem exists_actual_atomic_intercept_path
--       {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
--       [MeasurableSpace ι] [MeasurableSingletonClass ι]
--       {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
--       (hKi : (interior K).Nonempty)
--       (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
--       (y z : ι → E d) (R : ℝ≥0)
--       (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
--       (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
--         Function.Injective (fun i => (1-t) • y i + t • z i)) :
--       ∃ c r : ι → ℝ → ℝ,
--         (∀ i, Measurable (c i)) ∧
--         (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
--         (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
--         (∀ t ∈ Ioo 0 1, ∀ i,
--           (uniformMeasure K).real (CellGeometry.closedCell K
--             (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
--         (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
--         ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
--           162 * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem358.CellGeometry.closedCell` (definitions bundle `OAIQ5T2000` of this split); `OAI.Problem358.E` and `OAI.Problem358.uniformMeasure` (the published bundle `Def_Brenier`).
--
--   **Used by.** The proof of `OAI.Problem358.one_third_stability` of this split imports it.
-- source:
--   OpenAI, Sharp One-Third Stability of Brenier Maps, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 374; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Brenier/Brenier/CanonicalPaths.lean (declaration OAI.Problem358.FixedMassIntercepts.exists_actual_atomic_intercept_path)

import Mathlib
import Definitions.Def_Brenier
import Definitions.Def_OAIQ5T2000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace Problem358.FixedMassIntercepts

theorem exists_actual_atomic_intercept_path
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hKi : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y z : ι → E d) (R : ℝ≥0)
    (hbounded : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ R)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (fun i => (1-t) • y i + t • z i)) :
    ∃ c r : ι → ℝ → ℝ,
      (∀ i, Measurable (c i)) ∧
      (∀ i, ContinuousOn (r i) (Ioo 0 1)) ∧
      (∀ i t, t ∈ Ioo 0 1 → HasDerivAt (c i) (r i t) t) ∧
      (∀ t ∈ Ioo 0 1, ∀ i,
        (uniformMeasure K).real (CellGeometry.closedCell K
          (fun j => (1-t) • y j + t • z j) (fun j => c j t) i) = m i) ∧
      (∀ t ∈ Ioo 0 1, (∑ i, m i * c i t) = 0) ∧
      ∀ t ∈ Ioo 0 1, (∑ i, m i * r i t ^ 2) ≤
        162 * (R : ℝ) ^ 2 * ∑ i, m i * ‖y i-z i‖ ^ 2 := by
  sorry

end Problem358.FixedMassIntercepts

end

end OAI
end
