-- Prove2me | Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_spatial_witness_BK_scales
-- name    : OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:04.437338+00:00
-- url     : https://prove2.me/theorems/6e93f980-a455-417f-9a1f-2d6bdcfe8a18
-- title:
--   OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales` of [lean/OAI/Probability/GammaPassage/SpatialWitnessProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/SpatialWitnessProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP.CrossingBridge`, with `open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem gamma_spatial_witness_BK_scales (henv : GammaEnvironment shape rate P τ)
--       (hshape : 0 < shape) (hrate : 0 < rate)
--       (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
--       (N : ℕ) (S D : ℝ) :
--       ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
--         D*(2 : ℝ)^k ≤ (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k : ℝ) ∧
--         ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths
--           (spatialListSupport b k (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) is)
--           (is.map (spatialWitnessFamily b ((gammaMeanNorm henv hshape hrate) (direction b))
--             (extremeSlope (gammaMeanNorm henv hshape hrate) b false) (extremeSlope (gammaMeanNorm henv hshape hrate) b true)
--             (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k
--             (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k))) (fun e => τ e ω)} ≤
--           (2*q₀)^is.length
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm`, `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.extremeSlope`, `OAI.GammaFPP.BK.StrictDisjointPaths`, `OAI.GammaFPP.BK.StrictPathWitness`, `OAI.GammaFPP.CrossingBridge.characteristicExponent`, `OAI.GammaFPP.CrossingBridge.characteristicLength`, `OAI.GammaFPP.CrossingBridge.sourceCrossingK`, `OAI.GammaFPP.CrossingBridge.spatialListSupport` and `OAI.GammaFPP.CrossingBridge.spatialWitnessFamily` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment` and `OAI.PlanarFPP.Edge` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proof of `OAI.GammaFPP.gamma_differentiability` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/SpatialWitnessProbability.lean (declaration OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gamma_spatial_witness_BK_scales (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k : ℝ) ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths
        (spatialListSupport b k (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) is)
        (is.map (spatialWitnessFamily b ((gammaMeanNorm henv hshape hrate) (direction b))
          (extremeSlope (gammaMeanNorm henv hshape hrate) b false) (extremeSlope (gammaMeanNorm henv hshape hrate) b true)
          (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k
          (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k))) (fun e => τ e ω)} ≤
        (2*q₀)^is.length := by
  sorry

end GammaFPP.CrossingBridge

end OAI
end
