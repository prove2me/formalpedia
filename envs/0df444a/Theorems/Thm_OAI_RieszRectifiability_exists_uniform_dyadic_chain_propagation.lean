-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_uniform_dyadic_chain_propagation
-- name    : OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:25:14.104587+00:00
-- url     : https://prove2.me/theorems/9aabe3ae-f36f-4e9c-afd8-6adbafd263b0
-- title:
--   OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation` of [lean/OAI/Analysis/RieszRectifiability/Foundations/DyadicChainPropagation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Foundations/DyadicChainPropagation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`, `open scoped NNReal ENNReal`):
--
--   ```lean
--   theorem exists_uniform_dyadic_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
--       (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
--       (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
--       ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
--         GlobalUpperGrowth (p + 1) G μ →
--         (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
--           ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
--         ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
--         AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
--         (∀ l ≤ propagationHorizon J,
--           squaredExcess (p + 1) μ a (r * (2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
--         (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
--           MemLp (truncated (p + 1) μ η u) 2 μ ∧
--             eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
--         ∀ L : ℕ,
--         (∀ j < L, ScalarOscillationBound (p + 1) μ a
--           (descendantRadius r j * propagationTestRadius J)
--           (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) →
--         ∀ j ≤ L,
--           squaredExcess (p + 1) μ a (descendantRadius r j) ≤ propagationScale J ^ 2 ∧
--           (0 < j → bilateralBeta (p + 1) μ a (descendantRadius r j) < ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.GlobalUpperGrowth`, `OAI.RieszRectifiability.ScalarOscillationBound`, `OAI.RieszRectifiability.bilateralBeta`, `OAI.RieszRectifiability.descendantRadius`, `OAI.RieszRectifiability.propagationHorizon`, `OAI.RieszRectifiability.propagationScale`, `OAI.RieszRectifiability.propagationTestRadius` and `OAI.RieszRectifiability.squaredExcess` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.AdmissibleRadius`, `OAI.RieszRectifiability.Ambient` and `OAI.RieszRectifiability.truncated` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_selected_restart_uniform_deficit` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Foundations/DyadicChainPropagation.lean (declaration OAI.RieszRectifiability.exists_uniform_dyadic_chain_propagation)

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

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_dyadic_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G : ℝ) (hC : 0 < C) (b : ℝ) (hb1 : 1 < b) (hb2 : b ^ 2 < 2)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (J₀ : ℕ) :
    ∃ J : ℕ, J₀ ≤ J ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ s : ℝ, AdmissibleRadius μ s →
        ENNReal.ofReal (s ^ (p + 1) / C) ≤ μ (ball x s)) →
      ∀ a ∈ μ.support, ∀ r : ℝ, 0 < r →
      AdmissibleRadius μ (r * (2 : ℝ) ^ propagationHorizon J) →
      (∀ l ≤ propagationHorizon J,
        squaredExcess (p + 1) μ a (r * (2 : ℝ) ^ l) ≤ (propagationScale J * b ^ l) ^ 2) →
      (∀ η, 0 < η → ∀ u : Ambient d → ℝ, MemLp u 2 μ →
        MemLp (truncated (p + 1) μ η u) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) →
      ∀ L : ℕ,
      (∀ j < L, ScalarOscillationBound (p + 1) μ a
        (descendantRadius r j * propagationTestRadius J)
        (descendantRadius r j ^ (p + 2) * propagationScale J ^ 3)) →
      ∀ j ≤ L,
        squaredExcess (p + 1) μ a (descendantRadius r j) ≤ propagationScale J ^ 2 ∧
        (0 < j → bilateralBeta (p + 1) μ a (descendantRadius r j) < ε) := by
  sorry

end

end RieszRectifiability

end OAI
end
