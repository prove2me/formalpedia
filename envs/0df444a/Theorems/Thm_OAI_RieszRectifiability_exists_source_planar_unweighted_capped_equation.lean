-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_source_planar_unweighted_capped_equation
-- name    : OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:30.47403+00:00
-- url     : https://prove2.me/theorems/1b05a5fc-a6f2-48ec-ae85-08167106575e
-- title:
--   OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation` of [lean/OAI/Analysis/RieszRectifiability/Foundations/SourcePlanarUnweightedEquation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Foundations/SourcePlanarUnweightedEquation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_source_planar_unweighted_capped_equation {d : ℕ} (p : ℕ) (C G : ℝ)
--       (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
--       [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
--       (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
--       (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
--       (D : ℝ≥0)
--       (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
--         MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
--           eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
--       (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
--       (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
--       (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
--         (fun x => ENNReal.ofReal (f x))).map L = ν)
--       (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
--       (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
--       (cMass : ℝ) (hcMass : 0 < cMass)
--       (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
--       (hreflect : ScalarReflectionlessAt (p + 1) ν (L a)) :
--       ∃ s : ℕ → ℕ, StrictMono s ∧
--         Tendsto (fun j => (1 / 2 : ℝ) ^ (s j)) atTop (𝓝 0) ∧
--         ∃ b : ℝ, ∀ (g : Ambient (p + 1) → ℝ), Measurable g →
--           ∀ B : ℝ, (∀ x, |g x| ≤ B) → Integrable g volume →
--             (∀ x, g x ≠ 0 → x ∈ ball a H) →
--             Tendsto (fun j =>
--               (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R))
--                 e ((1 / 2 : ℝ) ^ (s j)) f x * g x) +
--               ∫ x, (∫ y in closedExterior a R, f y *
--                 inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x)
--               atTop (𝓝 (b * ∫ x, g x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarReflectionlessAt`, `OAI.RieszRectifiability.closedExterior` and `OAI.RieszRectifiability.scalarCappedTransform` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient`, `OAI.RieszRectifiability.kernel` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.source_planar_density_compact_fractional_equation` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Foundations/SourcePlanarUnweightedEquation.lean (declaration OAI.RieszRectifiability.exists_source_planar_unweighted_capped_equation)

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

theorem exists_source_planar_unweighted_capped_equation {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε f) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε f) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm f 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (e a : Ambient (p + 1)) (H R : ℝ) (hH : 0 < H) (hR : 0 < R) (hHR : 2 * H ≤ R)
    (hboundary : ν (frontier (ball (L a) R)) = 0) (hmass : ν (ball (L a) R) ≠ 0)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ENNReal.ofReal (cMass * (H / 4) ^ (p + 1)) ≤ ν (ball (L a) (H / 4)))
    (hreflect : ScalarReflectionlessAt (p + 1) ν (L a)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      Tendsto (fun j => (1 / 2 : ℝ) ^ (s j)) atTop (𝓝 0) ∧
      ∃ b : ℝ, ∀ (g : Ambient (p + 1) → ℝ), Measurable g →
        ∀ B : ℝ, (∀ x, |g x| ≤ B) → Integrable g volume →
          (∀ x, g x ≠ 0 → x ∈ ball a H) →
          Tendsto (fun j =>
            (∫ x, scalarCappedTransform (p + 1) (volume.restrict (ball a R))
              e ((1 / 2 : ℝ) ^ (s j)) f x * g x) +
            ∫ x, (∫ y in closedExterior a R, f y *
              inner ℝ e (kernel (p + 1) x y - kernel (p + 1) a y)) * g x)
            atTop (𝓝 (b * ∫ x, g x)) := by
  sorry

end

end RieszRectifiability

end OAI
end
