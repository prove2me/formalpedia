-- Prove2me | Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_characteristic_lengths_exist
-- name    : OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:55:15.920448+00:00
-- url     : https://prove2.me/theorems/f25d6fa6-8ea3-4f53-9aa4-96c59fde66cc
-- title:
--   OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist` of [lean/OAI/Probability/GammaPassage/CharacteristicLengths.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/CharacteristicLengths.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP.CrossingBridge`, with `open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem gamma_characteristic_lengths_exist (h : GammaEnvironment shape rate P τ)
--       (hshape : 0 < shape) (hrate : 0 < rate)
--       (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
--       ∀ᶠ k : ℕ in atTop,
--         characteristicExponent P τ shape rate (gammaMeanNorm h hshape hrate) b q k ≤ 3*k ∧
--         P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b)
--           ((2 : ℝ)^k) (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k) 0} ≤ q
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm`, `OAI.PlanarFPP.direction`, `OAI.GammaFPP.CrossingBridge.characteristicExponent`, `OAI.GammaFPP.CrossingBridge.characteristicLength`, `OAI.GammaFPP.CrossingBridge.crossingEvent` and `OAI.GammaFPP.CrossingBridge.sourceCrossingK` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment`, `OAI.PlanarFPP.Edge` and `OAI.PlanarFPP.Vertex` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proof of `OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/CharacteristicLengths.lean (declaration OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist)

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
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (τ : Edge → Ω → ℝ)

variable {P τ}

theorem gamma_characteristic_lengths_exist (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q : ℝ) (hb : |b| ≤ 1) (hq : 0 < q) :
    ∀ᶠ k : ℕ in atTop,
      characteristicExponent P τ shape rate (gammaMeanNorm h hshape hrate) b q k ≤ 3*k ∧
      P.real {ω | (fun e => τ e ω) ∈ crossingEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (sourceCrossingK shape rate (gammaMeanNorm h hshape hrate) b)
        ((2 : ℝ)^k) (characteristicLength P τ shape rate (gammaMeanNorm h hshape hrate) b q k) 0} ≤ q := by
  sorry

end GammaFPP.CrossingBridge

end OAI
end
