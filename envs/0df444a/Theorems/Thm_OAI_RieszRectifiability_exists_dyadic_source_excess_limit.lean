-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_source_excess_limit
-- name    : OAI.RieszRectifiability.exists_dyadic_source_excess_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:24:17.769208+00:00
-- url     : https://prove2.me/theorems/1108146e-a615-4482-b026-e1364e0db475
-- title:
--   OAI.RieszRectifiability.exists_dyadic_source_excess_limit: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_dyadic_source_excess_limit` of [lean/OAI/Analysis/RieszRectifiability/Limits/DyadicSourceExcessLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/DyadicSourceExcessLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Function Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_dyadic_source_excess_limit {p d : ℕ}
--       (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
--       (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
--       (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
--         ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
--       (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
--       (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
--       (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
--       (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
--       (M b : ℝ)
--       (hmoment : ∀ j l, l ≤ T j →
--         (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
--           M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
--       (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
--       (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
--       (D : ℝ≥0)
--       (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
--         MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
--           eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
--       (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
--       (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
--       ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 ≤ r →
--         Tendsto (fun j => squaredExcess (p + 1) (μ (ρ j)) 0 r / δ (ρ j) ^ 2) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.ScalarOscillationBound` and `OAI.RieszRectifiability.squaredExcess` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius`, `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/DyadicSourceExcessLimit.lean (declaration OAI.RieszRectifiability.exists_dyadic_source_excess_limit)

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

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal ENNReal

theorem exists_dyadic_source_excess_limit {p d : ℕ}
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth (p + 1) G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, AdmissibleRadius (μ j) r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ (μ j) (ball x r))
    (hdiam : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ENNReal.ofReal r ≤ ediam (μ j).support)
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support)
    (S : ℕ → AffineSubspace ℝ (Ambient d)) (hS : ∀ j, IsAffineNPlane (p + 1) (S j))
    (δ : ℕ → ℝ) (T : ℕ → ℕ) (hδ : Tendsto δ atTop (𝓝 0)) (hT : Tendsto T atTop atTop)
    (M b : ℝ)
    (hmoment : ∀ j l, l ≤ T j →
      (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l), infDist x (S j : Set (Ambient d)) ^ 2 ∂μ j) ≤
        M * (δ j * b ^ l) ^ 2 * ((2 : ℝ) ^ l) ^ (p + 1 + 2))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (δ j ^ 3))
    (D : ℝ≥0)
    (hB : ∀ j ε, 0 < ε → ∀ u : Ambient d → ℝ, MemLp u 2 (μ j) →
      MemLp (truncated (p + 1) (μ j) ε u) 2 (μ j) ∧
        eLpNorm (truncated (p + 1) (μ j) ε u) 2 (μ j) ≤ (D : ℝ≥0∞) * eLpNorm u 2 (μ j))
    (hδpos : ∀ j, 0 < δ j) (hb1 : 1 ≤ b) (hb2 : b < 2)
    (hlast : Tendsto (fun j => ((2 : ℝ) ^ T j)⁻¹ / δ j) atTop (𝓝 0)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∀ r : ℝ, 0 ≤ r →
      Tendsto (fun j => squaredExcess (p + 1) (μ (ρ j)) 0 r / δ (ρ j) ^ 2) atTop (𝓝 0) := by
  sorry

end

end RieszRectifiability

end OAI
end
