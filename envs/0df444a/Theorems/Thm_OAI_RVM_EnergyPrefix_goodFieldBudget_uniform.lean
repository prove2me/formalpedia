-- Prove2me | Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_uniform
-- name    : OAI.RVM.EnergyPrefix.goodFieldBudget_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:15:00.701339+00:00
-- url     : https://prove2.me/theorems/a514bf38-7d4d-4251-89e8-9e955c0b020d
-- title:
--   OAI.RVM.EnergyPrefix.goodFieldBudget_uniform: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.EnergyPrefix.goodFieldBudget_uniform` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceCellLast.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceCellLast.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   lemma EnergyPrefix.goodFieldBudget_uniform {s : Solution} {T lo hi I : ℝ}
--       (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
--       (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) (hlen : hi-lo≤I) :
--       (∑' j : ℕ, goodFieldBudget s X a k lo hi I j) ≤
--         (4*k+1:ℕ)*ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix`, `OAI.RVM.goodFieldBudget` and `OAI.RVM.totalEnergy` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proofs of `OAI.RVM.Admissible.bulk_source_uniform`, `OAI.RVM.Admissible.direct_remaining_source_deficit_short_uniform_expanded`, `OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded`, `OAI.RVM.Admissible.direct_source_deficit_short_sum`, `OAI.RVM.Admissible.direct_source_large_radius`, `OAI.RVM.Admissible.direct_source_relative_short_radial_sum`, `OAI.RVM.Admissible.direct_source_small_deficit_short_sum`, `OAI.RVM.Admissible.good_regular_double_sum`, `OAI.RVM.Admissible.good_structural_uniform`, `OAI.RVM.Admissible.projected_source_baseline_far`, `OAI.RVM.Admissible.projected_source_near_real_bin`, `OAI.RVM.Admissible.representative_regular_good_structural_double_sum`, `OAI.RVM.Admissible.small_good_uniform`, `OAI.RVM.Admissible.source_majorant_large_radius`, `OAI.RVM.Admissible.source_majorant_relative_short_radial_sum`, `OAI.RVM.Admissible.source_majorant_short_near_sum` and `OAI.RVM.Admissible.unselected_small_source_uniform` of this split import it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceCellLast.lean (declaration OAI.RVM.EnergyPrefix.goodFieldBudget_uniform)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Set

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma EnergyPrefix.goodFieldBudget_uniform {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) (hlen : hi-lo≤I) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j) ≤
      (4*k+1:ℕ)*ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  sorry

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

end

end OAI
end
