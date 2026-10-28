-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_UniversalDictionary_physicalOverlapLimsup_bound
-- name    : OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:57:54.055177+00:00
-- url     : https://prove2.me/theorems/d739b65d-920e-48ba-8985-4ab4c1b07cab
-- title:
--   OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalOverlapLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalOverlapLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.UniversalDictionary`, with `open _root_.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir`, `open ReducedTopology Filter Set`, `open scoped NNReal BigOperators Topology`):
--
--   ```lean
--   lemma physicalOverlapLimsup_bound {M : Model p} {C H : ℝ}
--       {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
--       (S : ReducedTopology) {η : ℝ} (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L+1:ℕ)) :
--       (η/8)*physicalOverlapLimsup M C H L Ns us S η≤
--         Real.sqrt (physicalShapeLimsup M C H L Ns us S (η/8))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.ReducedTopology`, `OAI.DilutedSpinGlass.UniversalDictionary.FullShapeControl`, `OAI.DilutedSpinGlass.UniversalDictionary.Spec`, `OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup` and `OAI.DilutedSpinGlass.UniversalDictionary.physicalShapeLimsup` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Model` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proofs of `OAI_DilutedSpinGlass_UniversalDictionary_physicalOverlapLimsup_tendsto` and `OAI.DilutedSpinGlass.UniversalDictionary.physicalSubtree_limsup_tendsto` of this split import it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/PhysicalOverlapLimit.lean (declaration OAI.DilutedSpinGlass.UniversalDictionary.physicalOverlapLimsup_bound)

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

lemma physicalOverlapLimsup_bound {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L+1:ℕ)) :
    (η/8)*physicalOverlapLimsup M C H L Ns us S η≤
      Real.sqrt (physicalShapeLimsup M C H L Ns us S (η/8)) := by
  sorry

end DilutedSpinGlass.UniversalDictionary

end

end OAI
end
