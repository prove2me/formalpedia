-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_full_planar_measure_limit
-- name    : OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:15.978678+00:00
-- url     : https://prove2.me/theorems/60daac6c-b963-4d82-88fa-661fe754957a
-- title:
--   OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit` of [lean/OAI/Analysis/RieszRectifiability/Limits/DyadicFullPlanarMeasureLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/DyadicFullPlanarMeasureLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_dyadic_full_planar_measure_limit {p d : ℕ}
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
--       (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hv : Tendsto v atTop (𝓝 0))
--       (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j)) :
--       ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
--         ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
--         ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
--         ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
--           IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
--           CompactTestConvergence (fun j => μ (ρ j)) ν ∧
--           GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
--           (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
--             ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
--           ν.support = (Llim.toLinearMap.range : Set (Ambient d)) ∧
--           (0 : Ambient d) ∈ ν.support ∧
--           (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
--             (∀ x, intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) ≤ f x ∧
--               f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
--             ((volume : Measure (Ambient (p + 1))).withDensity
--               (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
--           Tendsto a atTop (𝓝 0) ∧
--           Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
--           (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
--           (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
--           (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
--             N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
--           (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
--             ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
--           (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
--             MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
--               ((μ (ρ j)).restrict (ball 0 R))) ∧
--           (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
--             (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
--               normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
--               δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
--           ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.ScalarReflectionlessAt`, `OAI.RieszRectifiability.intrinsicGrowthDensityBound`, `OAI.RieszRectifiability.intrinsicLowerDensityBound` and `OAI.RieszRectifiability.normalCoordinate` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius` and `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proofs of `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy` and `OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation` of this split import it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/DyadicFullPlanarMeasureLimit.lean (declaration OAI.RieszRectifiability.exists_dyadic_full_planar_measure_limit)

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

theorem exists_dyadic_full_planar_measure_limit {p d : ℕ}
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
    (A v : ℕ → ℝ) (hA : Tendsto A atTop atTop) (hv : Tendsto v atTop (𝓝 0))
    (hosc : ∀ j, ScalarOscillationBound (p + 1) (μ j) 0 (A j) (v j)) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      ∃ a : ℕ → Ambient d, ∃ L : ℕ → Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
      ∃ N : ℕ → Ambient (d - (p + 1)) →ₗᵢ[ℝ] Ambient d,
      ∃ Llim : Ambient (p + 1) →ₗᵢ[ℝ] Ambient d,
        IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
        CompactTestConvergence (fun j => μ (ρ j)) ν ∧
        GlobalUpperGrowth (p + 1) (G * 2 ^ (p + 1)) ν ∧
        (∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
          ENNReal.ofReal (r ^ (p + 1) / (C * 4 ^ (p + 1))) ≤ ν (ball x r)) ∧
        ν.support = (Llim.toLinearMap.range : Set (Ambient d)) ∧
        (0 : Ambient d) ∈ ν.support ∧
        (∃ f : Ambient (p + 1) → ℝ, Measurable f ∧
          (∀ x, intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) ≤ f x ∧
            f x ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1))) ∧
          ((volume : Measure (Ambient (p + 1))).withDensity
            (fun x => ENNReal.ofReal (f x))).map Llim = ν) ∧
        Tendsto a atTop (𝓝 0) ∧
        Tendsto (fun j => (L j).toContinuousLinearMap) atTop (𝓝 Llim.toContinuousLinearMap) ∧
        (∀ j, a j ∈ S (ρ j)) ∧ (∀ j, (L j).toLinearMap.range = (S (ρ j)).direction) ∧
        (∀ j y, (L j).toContinuousLinearMap.adjoint (N j y) = 0) ∧
        (∀ j y, L j ((L j).toContinuousLinearMap.adjoint y) +
          N j ((N j).toContinuousLinearMap.adjoint y) = y) ∧
        (∀ j x, infDist x (S (ρ j) : Set (Ambient d)) =
          ‖(N j).toContinuousLinearMap.adjoint (x - a j)‖) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j : ℕ, ∀ R : ℝ, 0 < R →
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 R))) ∧
        (∀ i : Fin (d - (p + 1)), ∀ j l, l ≤ T (ρ j) →
          (∫ x in ball (0 : Ambient d) ((2 : ℝ) ^ l),
            normalCoordinate (a j) (N j) i x ^ 2 ∂μ (ρ j)) ≤
            δ (ρ j) ^ 2 * M * ((2 : ℝ) ^ l) ^ (p + 1) * ((2 : ℝ) ^ l * b ^ l) ^ 2) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  sorry

end

end RieszRectifiability

end OAI
end
