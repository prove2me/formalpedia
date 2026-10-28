-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_ConcreteReservoir_uniform_increment_sat
-- name    : OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:17:30.978991+00:00
-- url     : https://prove2.me/theorems/82e2b7c5-ed40-421c-a821-847e85fdbe3c
-- title:
--   OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment` of [lean/OAI/Probability/DilutedSpin/ExternalRoot.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ExternalRoot.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.ConcreteReservoir`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   lemma uniform_increment_sat (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
--       (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
--       (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H) (hm : ∀ l, 0 < m l)
--       (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
--       (N : ℕ) (u : K×ℕ → ℝ) :
--       |increment ν Q m D E M N u| ≤ Real.log 2+H+(2*p+1)*C*M.alpha+3
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath` and `OAI.DilutedSpinGlass.ConcreteReservoir.increment` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ExternalRoot.lean (declaration OAI.DilutedSpinGlass.ConcreteReservoir.uniform_increment)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.ConcreteReservoir
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot
open scoped NNReal BigOperators Topology
variable {K : Type} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
  {A : K → Type} [∀ q, Fintype (A q)] {L p : ℕ}
  (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
  (Q : (q : K) → Fin (L+1) → FiniteLaw (A q)) (m : Fin (L+1) → ℝ)
  (D E : (q : K) → Spin → FinitePath (A q) (L+1) → ℝ)

omit [DecidableEq K] in
lemma uniform_increment_sat (M : Model p) {C H : ℝ} (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hθ : ∀ᵐ z ∂M.disorder.toMeasure, ∀ σ, |z.1 σ| ≤ C)
    (hh : ∀ᵐ h ∂M.field.toMeasure, |h| ≤ H) (hm : ∀ l, 0 < m l)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1)
    (N : ℕ) (u : K×ℕ → ℝ) :
    |increment ν Q m D E M N u| ≤ Real.log 2+H+(2*p+1)*C*M.alpha+3 := by
  sorry

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end
