-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_source_planar_density_compact_fractional_equation
-- name    : OAI.RieszRectifiability.source_planar_density_compact_fractional_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:33.14849+00:00
-- url     : https://prove2.me/theorems/ccaf2b7c-8c73-4185-8f75-9ac7499d8080
-- title:
--   OAI.RieszRectifiability.source_planar_density_compact_fractional_equation: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.source_planar_density_compact_fractional_equation` of [lean/OAI/Analysis/RieszRectifiability/Limits/SourceDensityCompactEquation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/SourceDensityCompactEquation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory SchwartzMap Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem source_planar_density_compact_fractional_equation {d : ℕ} (p : ℕ) (C G : ℝ)
--       (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
--       [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
--       (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
--       (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
--       (D : ℝ≥0)
--       (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
--         MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
--           eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
--       (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
--       (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
--       (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
--       (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
--         (fun x => ENNReal.ofReal (f x))).map L = ν)
--       (cMass : ℝ) (hcMass : 0 < cMass)
--       (hlowerMass : ∀ r : ℝ, 0 < r →
--         ENNReal.ofReal (cMass * r ^ (p + 1)) ≤ ν (ball 0 r))
--       (hreflect : ScalarReflectionlessAt (p + 1) ν 0)
--       (ψ : 𝓢(Ambient (p + 1), ℝ)) (hψc : HasCompactSupport ψ) :
--       Integrable (fun y => f y * ((-1 / 2 : ℝ) *
--         ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
--         (∫ y, f y * ((-1 / 2 : ℝ) *
--           ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarReflectionlessAt` and `OAI.RieszRectifiability.fractionalSchwartzKernel` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/SourceDensityCompactEquation.lean (declaration OAI.RieszRectifiability.source_planar_density_compact_fractional_equation)

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

open MeasureTheory SchwartzMap Metric Set Filter Topology
open scoped NNReal ENNReal

theorem source_planar_density_compact_fractional_equation {d : ℕ} (p : ℕ) (C G : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hgrowth : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (hgν : GlobalUpperGrowth (p + 1) G ν) (hweak : CompactTestConvergence μ ν)
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (L : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d) (f : Ambient (p + 1) → ℝ)
    (hf : Measurable f) (c : ℝ) (hc : 0 < c) (hlower : ∀ x, c ≤ f x)
    (M : ℝ) (hupper : ∀ x, |f x| ≤ M)
    (hdensity : ((volume : Measure (Ambient (p + 1))).withDensity
      (fun x => ENNReal.ofReal (f x))).map L = ν)
    (cMass : ℝ) (hcMass : 0 < cMass)
    (hlowerMass : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (cMass * r ^ (p + 1)) ≤ ν (ball 0 r))
    (hreflect : ScalarReflectionlessAt (p + 1) ν 0)
    (ψ : 𝓢(Ambient (p + 1), ℝ)) (hψc : HasCompactSupport ψ) :
    Integrable (fun y => f y * ((-1 / 2 : ℝ) *
      ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) volume ∧
      (∫ y, f y * ((-1 / 2 : ℝ) *
        ∫ h, fractionalSchwartzKernel (p + 1) ψ y h)) = 0 := by
  sorry

end

end RieszRectifiability

end OAI
end
