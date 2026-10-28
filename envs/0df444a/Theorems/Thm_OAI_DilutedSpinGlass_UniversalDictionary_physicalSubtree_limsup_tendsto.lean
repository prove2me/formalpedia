-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physicalSubtree_limsup_tendsto
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:26.360982+00:00
-- url     : https://prove2.me/theorems/9259b3e7-7921-40e6-82d1-7b8e05df2199
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalSubtreeConcentration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalSubtreeConcentration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology Filter Set`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   theorem physicalSubtree_limsup_tendsto (M : Model p) (C H : ℝ)
--       (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
--       (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (K k : ℕ) :
--       Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
--         (subtreePotential K (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
--         k (single (L+1))) atTop) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.PrescribedTree.grid`, `OAI.DilutedSpinGlass.PrescribedTree.qExpect`, `OAI.DilutedSpinGlass.PrescribedTree.single`, `OAI.DilutedSpinGlass.PrescribedTree.subtreePotential`, `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec` and `OAI.DilutedSpinGlass.UniversalDictionary.physicalTreeVariance` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Model` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.UniversalDictionary.poissonInsertionOn_comparison_tendsto_ae` of this split imports it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalSubtreeConcentration.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto)

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

theorem physicalSubtree_limsup_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L)) (K k : ℕ) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (subtreePotential K (physicalTreeVariance M C H (Ns L n+1) L (us L n)))
      k (single (L+1))) atTop) atTop (𝓝 0) := by
  sorry

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
