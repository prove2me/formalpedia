-- Prove2me | Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_finite
-- name    : OAI.RVM.EnergyPrefix.goodFieldBudget_finite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:57.758624+00:00
-- url     : https://prove2.me/theorems/e3911fb5-5c4f-470c-bde3-3c3098a3e99c
-- title:
--   OAI.RVM.EnergyPrefix.goodFieldBudget_finite: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.EnergyPrefix.goodFieldBudget_finite` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceCellLast.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceCellLast.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open MeasureTheory Set`, `open Filter Set`, `open scoped Topology`, `open scoped Topology Pointwise`, `open Set MeasureTheory Metric ODE`, `open scoped Topology NNReal`, `open scoped ContDiff`, `open Set MeasureTheory Metric`, `open Set MeasureTheory`, `open Set MeasureTheory Metric Filter ODE`, `open Set MeasureTheory Filter Metric ODE`, `open Set MeasureTheory Filter Metric`, `open scoped Topology NNReal ContDiff`, `open Set MeasureTheory Filter`, `open scoped Topology ContDiff RealInnerProductSpace NNReal`, `open Set Filter MeasureTheory Metric`, `open scoped Topology ContDiff NNReal RealInnerProductSpace`, `open scoped Topology ContDiff NNReal`, `open scoped Topology ContDiff RealInnerProductSpace`, `open scoped Topology ContDiff NNReal ENNReal`, `open scoped Topology ContDiff`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`, `open Set`, `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff ENNReal`):
--
--   ```lean
--   lemma EnergyPrefix.goodFieldBudget_finite {s : Solution} {T lo hi I : ℝ}
--       (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
--       (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) :
--       (∑' j : ℕ, goodFieldBudget s X a k lo hi I j)≠⊤
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.EnergyPrefix` and `OAI.RVM.goodFieldBudget` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.Admissible.direct_source_shared_short_angles_expanded` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/SourceCellLast.lean (declaration OAI.RVM.EnergyPrefix.goodFieldBudget_finite)

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

lemma EnergyPrefix.goodFieldBudget_finite {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j)≠⊤ := by
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
