-- Prove2me | Theorems.Thm_OAI_PlanarFPP_exponential_source_connector_test
-- name    : OAI.PlanarFPP.exponential_source_connector_test
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:42:21.127964+00:00
-- url     : https://prove2.me/theorems/65ed0373-a208-488d-83dd-9ac27959e446
-- title:
--   OAI.PlanarFPP.exponential_source_connector_test: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.exponential_source_connector_test` of [lean/OAI/Probability/FirstPassage/ConnectorProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/ConnectorProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Filter MeasureTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exponential_source_connector_test {Ω : Type*} [MeasurableSpace Ω]
--       {P : Measure Ω} {τ : Edge → Ω → ℝ} (h : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
--       (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
--       ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
--         ∀ X : ℤ, ∀ Y a : ℝ, 1 ≤ a → a ≤ 2 →
--         P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent
--           (connectorVertices b X ⌈D0*s⌉ Y (trialWindow M R s) s)
--           (connectorWindow b X Y (trialWindow M R s))
--           (connectorWindow b (X+⌈D0*s⌉)
--             (Y+contactSign plus*a*trialWindow M R s) (trialWindow M R s))
--           (sourceSupportCost μ b plus ε s)} < κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.contactSign` and `OAI.PlanarFPP.trialWindow` (definitions bundle `OAISPf001` of this split); `OAI.PlanarFPP.allPairsRegionEvent`, `OAI.PlanarFPP.connectorVertices`, `OAI.PlanarFPP.connectorWindow` and `OAI.PlanarFPP.sourceSupportCost` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane` and `OAI.PlanarFPP.TimeConstantNorm` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proofs of `OAI.PlanarFPP.exponential_characteristic_lengths_exist` and `OAI.PlanarFPP.exponential_coarsePair_bound` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/ConnectorProbability.lean (declaration OAI.PlanarFPP.exponential_source_connector_test)

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

theorem exponential_source_connector_test {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {τ : Edge → Ω → ℝ} (h : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ X : ℤ, ∀ Y a : ℝ, 1 ≤ a → a ≤ 2 →
      P.real {ω | (fun e => τ e ω) ∉ allPairsRegionEvent
        (connectorVertices b X ⌈D0*s⌉ Y (trialWindow M R s) s)
        (connectorWindow b X Y (trialWindow M R s))
        (connectorWindow b (X+⌈D0*s⌉)
          (Y+contactSign plus*a*trialWindow M R s) (trialWindow M R s))
        (sourceSupportCost μ b plus ε s)} < κ := by
  sorry

end PlanarFPP

end OAI
end
