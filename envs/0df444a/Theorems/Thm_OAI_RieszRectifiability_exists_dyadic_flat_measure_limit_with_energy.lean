-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_dyadic_flat_measure_limit_with_energy
-- name    : OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:41.346372+00:00
-- url     : https://prove2.me/theorems/009d7c39-ee44-4e2f-98ac-df07326bb654
-- title:
--   OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy` of [lean/OAI/Analysis/RieszRectifiability/Limits/DyadicFlatEnergyLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/DyadicFlatEnergyLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set Filter Topology`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_dyadic_flat_measure_limit_with_energy {p d : ℕ}
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
--               (fun x => ENNReal.ofReal (f x))).map Llim = ν ∧
--             ∃ q : ℝ, 0 < q ∧
--               (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) ≤ q ∧
--               q ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) ∧
--               (∀ᵐ x ∂volume, f x = q) ∧
--               ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map Llim) ∧
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
--           (∀ i : Fin (d - (p + 1)), ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
--             MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
--               ((μ (ρ j)).restrict (ball 0 r)) ∧
--             (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B ∧
--             Integrable (fun v : Ambient d × Ambient d =>
--               fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
--               (((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ∧
--             (∫ v : Ambient d × Ambient d,
--               fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
--                 ∂((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ≤ E) ∧
--           (∀ i : Fin (d - (p + 1)), ∀ π : Ambient d → Fin (p + 1) → ℝ, ∀ K : ℝ≥0,
--             ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
--               MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
--                 ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) ∧
--               (∫ x in boundedProjectionRegion π 0 K H,
--                 (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B H ∧
--               Integrable (fun v : Ambient d × Ambient d =>
--                 fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
--                 (((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
--                   ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ∧
--               (∫ v : Ambient d × Ambient d,
--                 fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
--                   ∂((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
--                     ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ≤ E H) ∧
--           ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.CompactTestConvergence`, `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.ScalarReflectionlessAt`, `OAI.RieszRectifiability.boundedProjectionRegion`, `OAI.RieszRectifiability.fractionalPairEnergy`, `OAI.RieszRectifiability.intrinsicGrowthDensityBound`, `OAI.RieszRectifiability.intrinsicLowerDensityBound` and `OAI.RieszRectifiability.normalCoordinate` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius`, `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.exists_dyadic_source_excess_limit` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Limits/DyadicFlatEnergyLimit.lean (declaration OAI.RieszRectifiability.exists_dyadic_flat_measure_limit_with_energy)

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

theorem exists_dyadic_flat_measure_limit_with_energy {p d : ℕ}
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
            (fun x => ENNReal.ofReal (f x))).map Llim = ν ∧
          ∃ q : ℝ, 0 < q ∧
            (intrinsicLowerDensityBound (p + 1) (C * 4 ^ (p + 1)) : ℝ) ≤ q ∧
            q ≤ intrinsicGrowthDensityBound (p + 1) (G * 2 ^ (p + 1)) ∧
            (∀ᵐ x ∂volume, f x = q) ∧
            ν = ENNReal.ofReal q • (volume : Measure (Ambient (p + 1))).map Llim) ∧
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
        (∀ i : Fin (d - (p + 1)), ∀ r : ℝ, 0 < r → ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ j,
          MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
            ((μ (ρ j)).restrict (ball 0 r)) ∧
          (∫ x in ball 0 r, (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B ∧
          Integrable (fun v : Ambient d × Ambient d =>
            fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
            (((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ∧
          (∫ v : Ambient d × Ambient d,
            fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
              ∂((μ (ρ j)).restrict (ball 0 r)).prod ((μ (ρ j)).restrict (ball 0 r))) ≤ E) ∧
        (∀ i : Fin (d - (p + 1)), ∀ π : Ambient d → Fin (p + 1) → ℝ, ∀ K : ℝ≥0,
          ∃ B E : ℕ → ℝ, ∀ H, 0 ≤ B H ∧ 0 ≤ E H ∧ ∀ j,
            MemLp (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) 2
              ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)) ∧
            (∫ x in boundedProjectionRegion π 0 K H,
              (normalCoordinate (a j) (N j) i x / δ (ρ j)) ^ 2 ∂μ (ρ j)) ≤ B H ∧
            Integrable (fun v : Ambient d × Ambient d =>
              fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2)
              (((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
                ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ∧
            (∫ v : Ambient d × Ambient d,
              fractionalPairEnergy (p + 1) (fun x => normalCoordinate (a j) (N j) i x / δ (ρ j)) v.1 v.2
                ∂((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H)).prod
                  ((μ (ρ j)).restrict (boundedProjectionRegion π 0 K H))) ≤ E H) ∧
        ∀ c : Ambient d, ScalarReflectionlessAt (p + 1) ν c := by
  sorry

end

end RieszRectifiability

end OAI
end
