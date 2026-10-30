-- Prove2me | Theorems.Thm_OAI_Falconer_controlled_endpoint_angular_gain
-- name    : OAI.Falconer.controlled_endpoint_angular_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T21:46:09.695397+00:00
-- url     : https://prove2.me/theorems/456e68f9-64be-4266-94ba-7d0a3cbf6b90
-- title:
--   OAI.Falconer.controlled_endpoint_angular_gain: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Falconer.falconer_distance_conjecture`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Falconer.controlled_endpoint_angular_gain` of [lean/OAI/MeasureTheory/Falconer/Estimates/ControlledEndpointGain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/ControlledEndpointGain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Falconer`, with `open Set MeasureTheory NormedSpace`, `open scoped ENNReal`):
--
--   ```lean
--   theorem controlled_endpoint_angular_gain {h N : ℕ} {t : ℝ}
--       {κ : Type*} [Fintype κ] [DecidableEq κ]
--       (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
--       (ν₀ : Measure (Space (h+2)))
--       [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ν₀]
--       (hνeq : Measure.map gnomonicChart ν₀ = ν)
--       (B : Space h →ₗᵢ[ℝ] Space (h+3)) (w₀ : Sphere (h+3))
--       (E : Set (Space (h+3) × Sphere (h+3)))
--       (J : Sphere (h+3) → Finset κ) (v : κ → Space (h+3))
--       (G : Set (Space (h+2) × Space (h+2))) (hG : MeasurableSet G)
--       {ρ Lt Lq K C₀ Nc a κ₀ C a₀ b Bpair Btriple : ℝ}
--       (hρ : 0 ≤ ρ) (hδρ : 1/(2:ℝ)^N ≤ ρ)
--       (hB : ∀ i, inner ℝ (w₀:Space (h+3)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
--       (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ)
--       (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2)
--       (hsmall : 2*(h:ℝ)*(1/(2:ℝ)^N) < 1)
--       (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
--       (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
--       (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t)
--       (hμball : ∀ x : Space (h+3), ∀ j : ℕ, j ≤ N →
--         μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
--       (hνball : ∀ x : Sphere (h+3), ∀ j : ℕ, j ≤ N →
--         ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^(h+1:ℝ)))
--       (hpair : ∀ᵐ u : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
--         0 ≤ inner ℝ (u.1:Space (h+3)) (u.2:Space (h+3)))
--       (hK : 1 ≤ K) (hNc : 0 < Nc)
--       (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀)
--       (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h (h+1:ℝ) ≤ C₀)
--       (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h (h+1:ℝ)|+1) ≤ C₀)
--       (hcard : ((N+1:ℕ):ℝ)*C₀ ≤ K) (hC₀ : C₀ ≤ K)
--       (hlarge : 4*(1+2*(2:ℝ)^h+1) ≤ K)
--       (ha : 0 ≤ a) (hC : 0 ≤ C) (hb : 0 < b)
--       (hBp : 0 < Bpair) (hBt : 0 < Btriple)
--       (ha₀ : 1 ≤ a₀) (haK : 4+4*(h:ℝ) ≤ a₀)
--       (hbad : ENNReal.ofReal Btriple+2*ENNReal.ofReal (K^6)*ENNReal.ofReal Bpair ≤
--         ENNReal.ofReal (b^3/(4*(K^6)^3)))
--       (hmass : (1/(2:ℝ)^N)^κ₀ ≤ b^3/(2*(K^6)^5))
--       (hcount : K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
--         (C*(1/(2:ℝ)^N))*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-1-κ₀))
--       (hcoef : K^6*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-κ₀))
--       (herror : 144*(h:ℝ)*(1/(2:ℝ)^N) ≤ 3*((1/(2:ℝ)^N)^a)^2)
--       (hbudget : ((1/(2:ℝ)^N)^(-1-κ₀))^3*((6*C+35)/(1/(2:ℝ)^N)^a)^6*
--         ((1/(2:ℝ)^N)^(-κ₀)*(6*(1/(2:ℝ)^N))^(t-(h:ℝ)))^2 < ((1/(2:ℝ)^N)^κ₀)^2)
--       (hbase :
--         ENNReal.ofReal b*volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N))+
--         (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
--           volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
--           ((∫⁻ A, endpointPairCost ν₀ (1/(2:ℝ)^N) G A
--             ∂(gaussianRows (h+3) h).restrict
--               (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
--                 ENNReal.ofReal Bpair)+
--         (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
--           volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
--           ((∫⁻ A, endpointTripleCost ν₀ (1/(2:ℝ)^N) (2*(1/(2:ℝ)^N)^a) G A
--             ∂(gaussianRows (h+3) h).restrict
--               (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
--                 ENNReal.ofReal Btriple) ≤ ENNReal.ofReal (1/(4*K)))
--       (hE : MeasurableSet E) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
--       (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
--       (hEb : ∀ u ∈ E, ‖u.1‖ ≤ 1/4) (hanchors : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4)
--       (hcover : ∀ u ∈ E, ∃ i ∈ J u.2,
--         ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) :
--       ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+2) ρ^h)*
--         (μ.prod ν) E < ENNReal.ofReal (1/K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Falconer.Space`, `OAI.Falconer.Sphere`, `OAI.Falconer.gnomonicChart` and `OAI.Falconer.perpendicularPart` (definitions bundle `OAIQ088F000` of this split); `OAI.Falconer.gaussianFrostmanFactor`, `OAI.Falconer.gaussianLocalBandConstant`, `OAI.Falconer.gaussianPairBandConstant` and `OAI.Falconer.gaussianVectorBandConstant` (definitions bundle `OAIQ088F001` of this split); `OAI.Falconer.coordinateBox`, `OAI.Falconer.endpointPairCost`, `OAI.Falconer.endpointTripleCost`, `OAI.Falconer.gaussianRowNeighborhood` and `OAI.Falconer.gaussianRows` (definitions bundle `OAIQ088F002` of this split).
--
--   **Used by.** The proofs of `OAI_Falconer_endpoint_dyadic_angular_gain` and `OAI.Falconer.endpoint_original_middle_pruning` of this split import it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Estimates/ControlledEndpointGain.lean (declaration OAI.Falconer.controlled_endpoint_angular_gain)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002

section

attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem controlled_endpoint_angular_gain {h N : ℕ} {t : ℝ}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (μ : Measure (Space (h+3))) (ν : Measure (Sphere (h+3)))
    (ν₀ : Measure (Space (h+2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ν₀]
    (hνeq : Measure.map gnomonicChart ν₀ = ν)
    (B : Space h →ₗᵢ[ℝ] Space (h+3)) (w₀ : Sphere (h+3))
    (E : Set (Space (h+3) × Sphere (h+3)))
    (J : Sphere (h+3) → Finset κ) (v : κ → Space (h+3))
    (G : Set (Space (h+2) × Space (h+2))) (hG : MeasurableSet G)
    {ρ Lt Lq K C₀ Nc a κ₀ C a₀ b Bpair Btriple : ℝ}
    (hρ : 0 ≤ ρ) (hδρ : 1/(2:ℝ)^N ≤ ρ)
    (hB : ∀ i, inner ℝ (w₀:Space (h+3)) (B (EuclideanSpace.basisFun (Fin h) ℝ i)) = 0)
    (hν : ∀ᵐ w ∂ν, dist w w₀ ≤ ρ)
    (hstable : (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2)
    (hsmall : 2*(h:ℝ)*(1/(2:ℝ)^N) < 1)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (hμmass : μ univ ≤ 1) (hνmass : ν univ ≤ 1)
    (hLt : 0 ≤ Lt) (hLq : 0 ≤ Lq) (ht : (h:ℝ) < t)
    (hμball : ∀ x : Space (h+3), ∀ j : ℕ, j ≤ N →
      μ (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lt*(1/(2:ℝ)^j)^t))
    (hνball : ∀ x : Sphere (h+3), ∀ j : ℕ, j ≤ N →
      ν (Metric.ball x (1/(2:ℝ)^j)) ≤ ENNReal.ofReal (Lq*(1/(2:ℝ)^j)^(h+1:ℝ)))
    (hpair : ∀ᵐ u : Sphere (h+3) × Sphere (h+3) ∂ν.prod ν,
      0 ≤ inner ℝ (u.1:Space (h+3)) (u.2:Space (h+3)))
    (hK : 1 ≤ K) (hNc : 0 < Nc)
    (hCpoint : (4*gaussianVectorBandConstant)^h*Lt*gaussianFrostmanFactor h t ≤ C₀)
    (hCdir : (2*gaussianPairBandConstant)^h*Lq*gaussianFrostmanFactor h (h+1:ℝ) ≤ C₀)
    (hCmass : (2*gaussianPairBandConstant)^h*(|Lq*gaussianFrostmanFactor h (h+1:ℝ)|+1) ≤ C₀)
    (hcard : ((N+1:ℕ):ℝ)*C₀ ≤ K) (hC₀ : C₀ ≤ K)
    (hlarge : 4*(1+2*(2:ℝ)^h+1) ≤ K)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hb : 0 < b)
    (hBp : 0 < Bpair) (hBt : 0 < Btriple)
    (ha₀ : 1 ≤ a₀) (haK : 4+4*(h:ℝ) ≤ a₀)
    (hbad : ENNReal.ofReal Btriple+2*ENNReal.ofReal (K^6)*ENNReal.ofReal Bpair ≤
      ENNReal.ofReal (b^3/(4*(K^6)^3)))
    (hmass : (1/(2:ℝ)^N)^κ₀ ≤ b^3/(2*(K^6)^5))
    (hcount : K^11*(Nc*(2*((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+
      (C*(1/(2:ℝ)^N))*((h+3:ℝ)*(2*ρ)+1)))^h) ≤ (1/(2:ℝ)^N)^(-1-κ₀))
    (hcoef : K^6*(4*a₀)^(t-(h:ℝ)) ≤ (1/(2:ℝ)^N)^(-κ₀))
    (herror : 144*(h:ℝ)*(1/(2:ℝ)^N) ≤ 3*((1/(2:ℝ)^N)^a)^2)
    (hbudget : ((1/(2:ℝ)^N)^(-1-κ₀))^3*((6*C+35)/(1/(2:ℝ)^N)^a)^6*
      ((1/(2:ℝ)^N)^(-κ₀)*(6*(1/(2:ℝ)^N))^(t-(h:ℝ)))^2 < ((1/(2:ℝ)^N)^κ₀)^2)
    (hbase :
      ENNReal.ofReal b*volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N))+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
        volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, endpointPairCost ν₀ (1/(2:ℝ)^N) G A
          ∂(gaussianRows (h+3) h).restrict
            (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
              ENNReal.ofReal Bpair)+
      (ENNReal.ofReal (K^6)*ENNReal.ofReal (K^3)*
        volume (coordinateBox h ((1/4)*((h+3:ℝ)*(2*ρ)+1)+1/(2:ℝ)^N)))*
        ((∫⁻ A, endpointTripleCost ν₀ (1/(2:ℝ)^N) (2*(1/(2:ℝ)^N)^a) G A
          ∂(gaussianRows (h+3) h).restrict
            (gaussianRowNeighborhood (fun i => B (EuclideanSpace.basisFun (Fin h) ℝ i)) ((h+3:ℝ)*(2*ρ))))/
              ENNReal.ofReal Btriple) ≤ ENNReal.ofReal (1/(4*K)))
    (hE : MeasurableSet E) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (hJN : ∀ w, ((J w).card : ℝ≥0∞) ≤ ENNReal.ofReal Nc)
    (hEb : ∀ u ∈ E, ‖u.1‖ ≤ 1/4) (hanchors : ∀ w, ∀ i ∈ J w, ‖v i‖ ≤ 1/4)
    (hcover : ∀ u ∈ E, ∃ i ∈ J u.2,
      ‖perpendicularPart (u.2:Space (h+3)) (u.1-v i)‖ ≤ C*(1/(2:ℝ)^N)) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant (h+2) ρ^h)*
      (μ.prod ν) E < ENNReal.ofReal (1/K) := by
  sorry

end Falconer

end OAI
end
