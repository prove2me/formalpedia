-- Prove2me | Theorems.Thm_OAI_Falconer_dyadic_original_slice_costs
-- name    : OAI.Falconer.dyadic_original_slice_costs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:47:18.42693+00:00
-- url     : https://prove2.me/theorems/2d629097-af54-4ab4-b857-9beb4f6b75cf
-- title:
--   OAI.Falconer.dyadic_original_slice_costs: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.dyadic_original_slice_costs` of [lean/OAI/MeasureTheory/Falconer/Slicing/DyadicSliceCosts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Slicing/DyadicSliceCosts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set Metric MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem dyadic_original_slice_costs
--       (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
--       (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
--       [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ)
--       {D ρ Lt Lq t q : ℝ} (hD : D < 1/2) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
--       (hδρ : 1/(2:ℝ)^N ≤ ρ)
--       (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
--       (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t) (hq : (h:ℝ) < q)
--       (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
--       (hμball : ∀ x : Space (n+1), ∀ j : ℕ, j ≤ N →
--         μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
--       (hνball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N →
--         ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q))
--       (hchart : ∀ᵐ z : Sphere (n+1) × Sphere (n+1) ∂ν.prod ν,
--         0 ≤ inner ℝ (z.1:Space (n+1)) (z.2:Space (n+1)))
--       {K C S Nc R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hNc : 0 < Nc) (hR : 0 < R)
--       (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C)
--       (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C)
--       (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C)
--       (hcard : ((N+1:ℕ):ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
--       (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
--       (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
--       (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
--       (a : κ → Space (n+1)) (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
--       (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
--         ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
--       (C₁ C₂ : (Fin h → Space (n+1)) → ℝ≥0∞) (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
--       (t₁ t₂ b : ℝ≥0∞) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
--       (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N))+
--         (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
--           ((∫⁻ A, C₁ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₁)+
--         (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
--           ((∫⁻ A, C₂ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₂) ≤
--         ENNReal.ofReal (1/(4*K))) :
--       ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
--         ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N),
--         C₁ A < t₁ ∧ C₂ A < t₂ ∧ b < gaussianPrunedPairMass μ ν (1/(2:ℝ)^N) (gaussianPruningRadius (N := N))
--           (fun i => ENNReal.ofReal (K^6*gaussianPruningWeight h t i))
--           (fun i => ENNReal.ofReal (K^3*gaussianPruningWeight h q i)) (ENNReal.ofReal (K^3))
--           (gaussianActiveRelation E J a R (ENNReal.ofReal (K^11*(Nc*(2*R)^h))) true) (A,z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space` and `OAI.Falconer.Sphere` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.gaussianFrostmanFactor`, `OAI.Falconer.gaussianLocalBandConstant`, `OAI.Falconer.gaussianPairBandConstant`, `OAI.Falconer.gaussianPruningRadius`, `OAI.Falconer.gaussianPruningWeight` and `OAI.Falconer.gaussianVectorBandConstant` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.coordinateBox`, `OAI.Falconer.gaussianActiveRelation`, `OAI.Falconer.gaussianPrunedPairMass`, `OAI.Falconer.gaussianRowNeighborhood` and `OAI.Falconer.gaussianRows` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proof of `OAI.Falconer.controlled_endpoint_angular_gain` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Slicing/DyadicSliceCosts.lean (declaration OAI.Falconer.dyadic_original_slice_costs)

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
open Set Metric MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem dyadic_original_slice_costs
    (B : Fin h → Space (n+1)) (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N : ℕ)
    {D ρ Lt Lq t q : ℝ} (hD : D < 1/2) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t) (hq : (h:ℝ) < q)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hμball : ∀ x : Space (n+1), ∀ j : ℕ, j ≤ N →
      μ (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (n+1), ∀ j : ℕ, j ≤ N →
      ν (ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^q))
    (hchart : ∀ᵐ z : Sphere (n+1) × Sphere (n+1) ∂ν.prod ν,
      0 ≤ inner ℝ (z.1:Space (n+1)) (z.2:Space (n+1)))
    {K C S Nc R : ℝ} (hK : 0 < K) (hS : 0 ≤ S) (hNc : 0 < Nc) (hR : 0 < R)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h q ≤ C)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h q|+1) ≤ C)
    (hcard : ((N+1:ℕ):ℝ)*C ≤ K) (hC : C ≤ K) (hlarge : 4*(1+2*S+1) ≤ K)
    (hfactor : ENNReal.ofReal ((2:ℝ)^h)*μ univ ≤ ENNReal.ofReal S)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hmean : ENNReal.ofReal (1/K) ≤ ENNReal.ofReal ((2:ℝ)^h)*
      ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E)
    (C₁ C₂ : (Fin h → Space (n+1)) → ℝ≥0∞) (hC₁ : Measurable C₁) (hC₂ : Measurable C₂)
    (t₁ t₂ b : ℝ≥0∞) (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (ht₁top : t₁ ≠ ∞) (ht₂top : t₂ ≠ ∞)
    (hbase : b*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N))+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, C₁ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₁)+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*volume (coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, C₂ A ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))))/t₂) ≤
      ENNReal.ofReal (1/(4*K))) :
    ∃ A ∈ gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ)),
      ∃ z ∈ coordinateBox h (D*((n+1:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N),
      C₁ A < t₁ ∧ C₂ A < t₂ ∧ b < gaussianPrunedPairMass μ ν (1/(2:ℝ)^N) (gaussianPruningRadius (N := N))
        (fun i => ENNReal.ofReal (K^6*gaussianPruningWeight h t i))
        (fun i => ENNReal.ofReal (K^3*gaussianPruningWeight h q i)) (ENNReal.ofReal (K^3))
        (gaussianActiveRelation E J a R (ENNReal.ofReal (K^11*(Nc*(2*R)^h))) true) (A,z) := by
  sorry

end Falconer

end OAI
end
