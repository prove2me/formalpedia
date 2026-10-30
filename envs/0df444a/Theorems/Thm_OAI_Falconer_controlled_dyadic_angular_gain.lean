-- Prove2me | Theorems.Thm_OAI_Falconer_controlled_dyadic_angular_gain
-- name    : OAI.Falconer.controlled_dyadic_angular_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:46:48.991964+00:00
-- url     : https://prove2.me/theorems/bd57ae8f-0f32-45ca-8262-6af237b474a3
-- title:
--   OAI.Falconer.controlled_dyadic_angular_gain: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.controlled_dyadic_angular_gain` of [lean/OAI/MeasureTheory/Falconer/Angular/ControlledAngularGain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/ControlledAngularGain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory NormedSpace`, `open scoped ENNReal`):
--
--   ```lean
--   theorem controlled_dyadic_angular_gain
--       (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q : ℝ}
--       (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
--       {C : ℝ} (hC : 0 ≤ C) :
--       ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
--       ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
--         (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
--         [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--         (w₀ : Sphere (h+2)) (B : Space h →ₗᵢ[ℝ] Space (h+2))
--         (E : Set (Space (h+2) × Sphere (h+2)))
--         (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2))
--         (ρ Lt Lq K C₀ Nc Z a₀ : ℝ),
--       1/(2:ℝ)^N < δ₀ → 0 ≤ ρ → 1/(2:ℝ)^N ≤ ρ →
--       (∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0) →
--       (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
--       (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 →
--       4*(h:ℝ)*(1/(2:ℝ)^N)+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 →
--       (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
--       0 ≤ Lt → 0 ≤ Lq →
--       (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
--         μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t)) →
--       (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
--         ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q)) →
--       (∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
--         0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2))) →
--       0 < K → 0 < Nc → 0 < Z →
--       (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀ →
--       (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C₀ →
--       (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C₀ →
--       ((N+1:ℕ):ℝ)*C₀ ≤ K → C₀ ≤ K → 4*(1+2*(2:ℝ)^h+1) ≤ K →
--       (1/4)*((h+2:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N ≤ Z →
--       1 ≤ a₀ → 1 ≤ 4*K^10*(2*Z)^h → 4+8*(h:ℝ) ≤ a₀ →
--       (4*K^10*(2*Z)^h)*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
--       (4*K^10*(2*Z)^h)*(8*a₀)^(q-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
--       (1/(2:ℝ)^N)^η < 1/(4*K^10*(2*Z)^h) →
--       K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
--         (C*(1/(2:ℝ)^N))*((h+2:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-(q-(h:ℝ))-η) →
--       MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
--       (∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc) →
--       (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
--       (∀ u ∈ E, ∃ i ∈ J u.2,
--         ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
--       ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+1) ρ^h)*
--         (μ.prod ν) E < ENNReal.ofReal (1/K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space`, `OAI.Falconer.Sphere` and `OAI.Falconer.perpendicularPart` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.gaussianFrostmanFactor`, `OAI.Falconer.gaussianLocalBandConstant`, `OAI.Falconer.gaussianPairBandConstant` and `OAI.Falconer.gaussianVectorBandConstant` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.PublishedPlanarFurstenberg` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI.Falconer.Regularization.nonendpoint_source_class_middle_pruning` and `OAI_Falconer_nonendpoint_middle_radial_pruning` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Angular/ControlledAngularGain.lean (declaration OAI.Falconer.controlled_dyadic_angular_gain)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem controlled_dyadic_angular_gain
    (hpublished : PublishedPlanarFurstenberg) {h : ℕ} {t q : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t) (ht : t-(h:ℝ) < 1)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (μ : Measure (Space (h+2))) (ν : Measure (Sphere (h+2)))
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (w₀ : Sphere (h+2)) (B : Space h →ₗᵢ[ℝ] Space (h+2))
      (E : Set (Space (h+2) × Sphere (h+2)))
      (J : Sphere (h+2) → Finset κ) (a : κ → Space (h+2))
      (ρ Lt Lq K C₀ Nc Z a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 ≤ ρ → 1/(2:ℝ)^N ≤ ρ →
    (∀ i, inner ℝ (w₀:Space (h+2)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0) →
    (∀ᵐ w ∂ν, dist w w₀ ≤ ρ) →
    (h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/2 →
    4*(h:ℝ)*(1/(2:ℝ)^N)+ρ+4*(h:ℝ)*((h+2:ℝ)*(2*ρ)) ≤ 1/4 →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) → μ univ ≤ 1 → ν univ ≤ 1 →
    0 ≤ Lt → 0 ≤ Lq →
    (∀ x : Space (h+2), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t)) →
    (∀ x : Sphere (h+2), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q)) →
    (∀ᵐ u : Sphere (h+2) × Sphere (h+2) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+2)) (u.2:Space (h+2))) →
    0 < K → 0 < Nc → 0 < Z →
    (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀ →
    (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C₀ →
    (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C₀ →
    ((N+1:ℕ):ℝ)*C₀ ≤ K → C₀ ≤ K → 4*(1+2*(2:ℝ)^h+1) ≤ K →
    (1/4)*((h+2:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N ≤ Z →
    1 ≤ a₀ → 1 ≤ 4*K^10*(2*Z)^h → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*(2*Z)^h)*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*(2*Z)^h)*(8*a₀)^(q-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*(2*Z)^h) →
    K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+2:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-(q-(h:ℝ))-η) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc) →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+2)) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+1) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  sorry

end Falconer

end OAI
end
