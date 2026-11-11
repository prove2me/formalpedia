-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_planar_full_support_of_reflectionless
-- name    : OAI.RieszRectifiability.planar_full_support_of_reflectionless
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:46.333715+00:00
-- url     : https://prove2.me/theorems/94a22faa-07fe-47ca-bc69-e48039fae449
-- title:
--   OAI.RieszRectifiability.planar_full_support_of_reflectionless: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.planar_full_support_of_reflectionless` of [lean/OAI/Analysis/RieszRectifiability/Rigidity/PlanarReflectionlessSupport.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/PlanarReflectionlessSupport.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem planar_full_support_of_reflectionless {p d : ℕ}
--       (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d)) (hne : ν ≠ 0)
--       (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
--       (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G ν)
--       (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
--         ENNReal.ofReal (r ^ (p + 1) / C) ≤ ν (ball x r))
--       (hreflect : ∀ a ∈ ν.support, ScalarReflectionlessAt (p + 1) ν a) :
--       (planarPullbackMeasure L ν).support = univ ∧
--         ν.support = (L.toLinearMap.range : Set (Ambient d))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarReflectionlessAt` and `OAI.RieszRectifiability.planarPullbackMeasure` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Rigidity/PlanarReflectionlessSupport.lean (declaration OAI.RieszRectifiability.planar_full_support_of_reflectionless)

import Mathlib
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem planar_full_support_of_reflectionless {p d : ℕ}
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (ν : Measure (Ambient d)) (hne : ν ≠ 0)
    (hs : ν.support ⊆ (L.toLinearMap.range : Set (Ambient d)))
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ ν (ball x r))
    (hreflect : ∀ a ∈ ν.support, ScalarReflectionlessAt (p + 1) ν a) :
    (planarPullbackMeasure L ν).support = univ ∧
      ν.support = (L.toLinearMap.range : Set (Ambient d)) := by
  sorry

end

end RieszRectifiability

end OAI
end
