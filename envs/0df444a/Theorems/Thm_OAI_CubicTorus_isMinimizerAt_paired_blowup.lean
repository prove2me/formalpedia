-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_paired_blowup
-- name    : OAI.CubicTorus.isMinimizerAt_paired_blowup
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:08:16.354907+00:00
-- url     : https://prove2.me/theorems/8b9565a9-3bb7-43ed-bfd5-55e29c6bbc27
-- title:
--   OAI.CubicTorus.isMinimizerAt_paired_blowup: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_paired_blowup` of [lean/OAI/Geometry/CubicTorus/Reflection/BVConeSecondaryFlux.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/BVConeSecondaryFlux.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_paired_blowup {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       (hH : ∀ D : WallVariation, normalFirstVariation μ D =
--         H*directionalFlux E D.coordinate D.function)
--       (c : Cover) {d : ℝ} (hd : 0 < d)
--       (hc : Metric.closedBall c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
--       (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
--       ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
--         (φ : ℕ → ℕ) (U : Ultrafilter ℕ),
--         MeasurableSet A ∧ 0 ≤ θ ∧ StrictMono φ ∧ (U : Filter ℕ) ≤ atTop ∧
--         Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
--           |blowupCharacteristic E c (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
--           atTop (𝓝 0) ∧
--         Tendsto (fun i ↦ blowupNormalMeasure μ c (r (φ i)) 2) U (𝓝 ν) ∧
--         (∀ ρ : ℝ, 0 < ρ → ρ < 2 →
--           (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) ∧
--         (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
--           tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
--           (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
--           (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
--             ∫ x in A, divergence F x) ∧
--         (∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
--           ⟪(z.2 : Cover),z.1⟫ = 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.WallVariation`, `OAI.CubicTorus.blowupCharacteristic`, `OAI.CubicTorus.blowupNormalMeasure`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.normalFirstVariation` and `OAI.CubicTorus.tangentialDivergence` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.divergence` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/BVConeSecondaryFlux.lean (declaration OAI.CubicTorus.isMinimizerAt_paired_blowup)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_paired_blowup {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (c : Cover) {d : ℝ} (hd : 0 < d)
    (hc : Metric.closedBall c d ⊆ {x | ∀ j, 0 < x j ∧ x j < 1})
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0)) :
    ∃ (A : Set Cover) (ν : FiniteMeasure BlowupNormalBundle) (θ : ℝ)
      (φ : ℕ → ℕ) (U : Ultrafilter ℕ),
      MeasurableSet A ∧ 0 ≤ θ ∧ StrictMono φ ∧ (U : Filter ℕ) ≤ atTop ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E c (r (φ i)) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      Tendsto (fun i ↦ blowupNormalMeasure μ c (r (φ i)) 2) U (𝓝 ν) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 2 →
        (ν : Measure BlowupNormalBundle).real {z | z.1 ∈ Metric.ball (0 : Cover) ρ} = θ*ρ^2) ∧
      (∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
        (∫ z, tangentialDivergence F z.1 z.2 ∂(ν : Measure BlowupNormalBundle)) = 0 ∧
        (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
          ∫ x in A, divergence F x) ∧
      (∀ᵐ z ∂(ν : Measure BlowupNormalBundle), z.1 ∈ Metric.ball (0 : Cover) 1 →
        ⟪(z.2 : Cover),z.1⟫ = 0) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
