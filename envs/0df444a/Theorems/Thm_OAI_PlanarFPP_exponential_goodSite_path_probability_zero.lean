-- Prove2me | Theorems.Thm_OAI_PlanarFPP_exponential_goodSite_path_probability_zero
-- name    : OAI.PlanarFPP.exponential_goodSite_path_probability_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:48.860986+00:00
-- url     : https://prove2.me/theorems/eda1a393-8d9b-475f-bd1f-086c4227a687
-- title:
--   OAI.PlanarFPP.exponential_goodSite_path_probability_zero: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.exponential_goodSite_path_probability_zero` of [lean/OAI/Probability/FirstPassage/GoodSitePaths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/GoodSitePaths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exponential_goodSite_path_probability_zero (h : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
--       (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
--       (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M) :
--       P {ω | infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
--         goodSiteEvent μ b A R ε s plus n d M v) 0}=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.goodSiteEvent` and `OAI.PlanarFPP.infiniteOrientedPath` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane`, `OAI.PlanarFPP.TimeConstantNorm` and `OAI.PlanarFPP.Vertex` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proofs of `OAI.PlanarFPP.exponential_characteristic_lengths_exist` and `OAI.PlanarFPP.exponential_coarsePair_bound` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/GoodSitePaths.lean (declaration OAI.PlanarFPP.exponential_goodSite_path_probability_zero)

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_goodSite_path_probability_zero (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M) :
    P {ω | infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent μ b A R ε s plus n d M v) 0}=0 := by
  sorry

end PlanarFPP

end OAI
end
