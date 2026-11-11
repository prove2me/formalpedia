-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_active_surface_successor_input_chart
-- name    : OAI.RieszRectifiability.active_surface_successor_input_chart
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:08.157089+00:00
-- url     : https://prove2.me/theorems/d8b715f2-2b38-4ad1-84c4-2e22a2b50ef3
-- title:
--   OAI.RieszRectifiability.active_surface_successor_input_chart: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.active_surface_successor_input_chart` of [lean/OAI/Analysis/RieszRectifiability/Restart/ActiveSurfaceChartInductionStep.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Restart/ActiveSurfaceChartInductionStep.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`, `open scoped NNReal`):
--
--   ```lean
--   theorem active_surface_successor_input_chart
--       (i : SupportCellDescendant μ R hR k z)
--       (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1)) :
--       HasActiveCellInputChart i (S i) A
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.HasActiveCellInputChart`, `OAI.RieszRectifiability.HasActiveSurfaceCharts`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.activeLevelIndex`, `OAI.RieszRectifiability.activeProjectionError`, `OAI.RieszRectifiability.activeRegionCell`, `OAI.RieszRectifiability.bilateralPlaneError`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.activeRegionSurface_charts` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Restart/ActiveSurfaceChartInductionStep.lean (declaration OAI.RieszRectifiability.active_surface_successor_input_chart)

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
open scoped NNReal

variable {n d : ℕ} (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
  (z : (supportLatticeNets μ R hR k).points)
  (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
  (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
  (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
  (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 128)
  (hfit : ∀ i, activeRegionCell Good i →
    bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
  (A : Set (Ambient d)) (hcharts : HasActiveSurfaceCharts μ R hR k z Good t S ε A)

include hS hε hεtiny hsmall hfit hcharts

theorem active_surface_successor_input_chart
    (i : SupportCellDescendant μ R hR k z)
    (hi : i ∈ activeLevelIndex μ R hR k z Good (t + 1)) :
    HasActiveCellInputChart i (S i) A := by
  sorry

end

end RieszRectifiability

end OAI
end
