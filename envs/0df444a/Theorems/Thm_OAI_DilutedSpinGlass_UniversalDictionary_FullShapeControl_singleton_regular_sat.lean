-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_FullShapeControl_singleton_regular_sat
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:20:29.905497+00:00
-- url     : https://prove2.me/theorems/cb6c3888-5174-4c1e-8339-e9f4d49cee4a
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular` of [lean/OAI/Probability/DilutedSpin/FullRegularSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/FullRegularSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology Filter Set`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   lemma FullShapeControl.singleton_regular_sat {M : Model p} {C H : ℝ}
--       {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
--       {η t : ℝ} (hη : 0<η) (ht : 0<t) : ∀ᶠ n in atTop,
--       ∀ d ∈ regularSingletonDepths L η,
--         physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d≤((L+1:ℕ):ℝ)⁻¹/η+t
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Model` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.gridExponents`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalSingletonEnergy` and `OAI.DilutedSpinGlass.UniversalDictionary.regularSingletonDepths` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/FullRegularSelection.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl.singleton_regular)

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
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
variable {p L : ℕ}

lemma FullShapeControl.singleton_regular_sat {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    {η t : ℝ} (hη : 0<η) (ht : 0<t) : ∀ᶠ n in atTop,
    ∀ d ∈ regularSingletonDepths L η,
      physicalSingletonEnergy (gridExponents L) M C H (Ns n+1) (us n) d≤((L+1:ℕ):ℝ)⁻¹/η+t := by
  sorry

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
