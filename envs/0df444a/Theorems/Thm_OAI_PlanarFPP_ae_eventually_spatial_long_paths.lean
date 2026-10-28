-- Prove2me | Theorems.Thm_OAI_PlanarFPP_ae_eventually_spatial_long_paths
-- name    : OAI.PlanarFPP.ae_eventually_spatial_long_paths
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:38.944111+00:00
-- url     : https://prove2.me/theorems/28a4afea-1670-4102-af74-ac0c5ef24213
-- title:
--   OAI.PlanarFPP.ae_eventually_spatial_long_paths: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.ae_eventually_spatial_long_paths` of [lean/OAI/Probability/FirstPassage/WitnessBorelCantelli.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/WitnessBorelCantelli.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Finset MeasureTheory Filter`):
--
--   ```lean
--   theorem ae_eventually_spatial_long_paths (henv : ExponentialEnvironment P τ)
--       (b m₀ am ap K η r : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
--       (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1)
--       (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
--       (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
--       (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
--       (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
--       (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
--         (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ (r^16)^is.length) :
--       ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
--         ∀ blocks : List (List Step), ∀ rest : List Step,
--         blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
--         (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
--         ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
--         N*η*(2 : ℝ)^k/2 ≤ defect (fun e => τ e ω) b m₀ ((am+ap)/2) 0 (blocks.flatten++rest)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.Traversal` (definitions bundle `OAISPf000` of this split); `OAI.PlanarFPP.FullSpatialChunk`, `OAI.PlanarFPP.StrictDisjointPaths`, `OAI.PlanarFPP.StrictPathWitness`, `OAI.PlanarFPP.chunkInterior`, `OAI.PlanarFPP.defect`, `OAI.PlanarFPP.spatialListSupport`, `OAI.PlanarFPP.spatialWitnessFamily`, `OAI.PlanarFPP.trace` and `OAI.PlanarFPP.traversalEdge` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.Step`, `OAI.PlanarFPP.Vertex` and `OAI.PlanarFPP.displacement` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proof of `OAI.PlanarFPP.actual_differentiable_horizontal` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/WitnessBorelCantelli.lean (declaration OAI.PlanarFPP.ae_eventually_spatial_long_paths)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_eventually_spatial_long_paths (henv : ExponentialEnvironment P τ)
    (b m₀ am ap K η r : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ (r^16)^is.length) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect (fun e => τ e ω) b m₀ ((am+ap)/2) 0 (blocks.flatten++rest) := by
  sorry

end PlanarFPP

end OAI
end
