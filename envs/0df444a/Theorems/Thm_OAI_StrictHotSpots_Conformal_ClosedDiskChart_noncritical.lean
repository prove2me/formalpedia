-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_noncritical
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:05:21.536738+00:00
-- url     : https://prove2.me/theorems/e9372763-e1f7-43c6-a1d1-1a4210e22cb1
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical` of [lean/OAI/Analysis/HotSpots/HotSpots/Main.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Main.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter Metric Function Module`, `open scoped ENNReal NNReal Topology InnerProductSpace`, `open PlaneGreen DiskH10`):
--
--   ```lean
--   theorem noncritical (hΩ : AdmissibleDomain Ω)
--       {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0) :
--       ∀ x ∈ Ω, gradient u x ≠ 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.Conformal.ClosedDiskChart` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace` and `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.main_theorem` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Main.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualNoncritical

noncomputable section
open Set MeasureTheory Filter Metric Function Module
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

include c

theorem noncritical (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∀ x ∈ Ω, gradient u x ≠ 0 := by
  sorry
end StrictHotSpots.Conformal.ClosedDiskChart

end
end ActualNoncritical

end OAI
end
