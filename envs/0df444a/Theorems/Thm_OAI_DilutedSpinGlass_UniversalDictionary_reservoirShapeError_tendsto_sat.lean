-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_reservoirShapeError_tendsto_sat
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:25.846912+00:00
-- url     : https://prove2.me/theorems/e4dca431-a4d1-4a1c-b7cc-c985a1597020
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto_sat: intermediate lemma from OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto` of [lean/OAI/Probability/DilutedSpin/ReservoirShapeLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ReservoirShapeLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology Filter Set`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   lemma reservoirShapeError_tendsto_sat (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
--       (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
--       (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
--       (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
--       Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
--         (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.Model` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.PrescribedTree.grid`, `OAI.DilutedSpinGlass.PrescribedTree.qExpect`, `OAI.DilutedSpinGlass.PrescribedTree.single`, `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec` and `OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeDeviation` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/ReservoirShapeLimit.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.reservoirShapeError_tendsto)

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
variable {p : ℕ}

lemma reservoirShapeError_tendsto_sat (M : Model p) (hα : 0<M.alpha) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (hNs : ∀ L, Tendsto (Ns L) atTop atTop)
    (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (reservoirShapeDeviation M C H (Ns L n+1) L (us L n)) k (single (L+1))) atTop)
      atTop (𝓝 0) := by
  sorry
end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
