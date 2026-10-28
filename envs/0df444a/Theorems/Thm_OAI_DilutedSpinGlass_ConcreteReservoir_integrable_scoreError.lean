-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_ConcreteReservoir_integrable_scoreError
-- name    : OAI.DilutedSpinGlass.ConcreteReservoir.integrable_scoreError
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:57.843192+00:00
-- url     : https://prove2.me/theorems/4492a673-0d74-4450-a64c-b7954a5343e6
-- title:
--   OAI.DilutedSpinGlass.ConcreteReservoir.integrable_scoreError: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.ConcreteReservoir.integrable_scoreError` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/ExternalRoot.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/ExternalRoot.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.ConcreteReservoir`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   lemma integrable_scoreError (π : Measure (K×ℕ → ℝ)) [IsProbabilityMeasure π]
--       (M : Model p) (C H : ℝ)
--       (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1) (j : K×ℕ) (N : ℕ) :
--       Integrable (scoreError ν Q m D E M C H j N) π
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath` and `OAI.DilutedSpinGlass.ConcreteReservoir.scoreError` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Model` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.UniversalDictionary.universal_analytic_selection` of this split imports it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/ExternalRoot.lean (declaration OAI.DilutedSpinGlass.ConcreteReservoir.integrable_scoreError)

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

lemma integrable_scoreError (π : Measure (K×ℕ → ℝ)) [IsProbabilityMeasure π]
    (M : Model p) (C H : ℝ)
    (hD : ∀ q σ y, |D q σ y| ≤ 1) (hE : ∀ q σ y, |E q σ y| ≤ 1) (j : K×ℕ) (N : ℕ) :
    Integrable (scoreError ν Q m D E M C H j N) π := by
  sorry

end DilutedSpinGlass.ConcreteReservoir
end

end

end OAI
end
