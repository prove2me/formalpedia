-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_eq_zero_of_boundary_closedGradient
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:10:00.265047+00:00
-- url     : https://prove2.me/theorems/8fc8673b-397b-44f4-9e50-0b2ef4afdd2b
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient` of [lean/OAI/Analysis/HotSpots/HotSpots/Cauchy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Cauchy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set Filter Metric Function`, `open scoped Topology ContDiff InnerProductSpace`):
--
--   ```lean
--   theorem eq_zero_of_boundary_closedGradient (hΩ : AdmissibleDomain Ω)
--       {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v)
--       (hvc : ContinuousOn v (closure Ω)) {Y : Plane → Plane}
--       (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
--       {p : Plane} (hp : p ∈ frontier Ω) {U : Set Plane} (hU : IsOpen U) (hpU : p ∈ U)
--       (hz : ∀ x ∈ U ∩ frontier Ω, v x = 0 ∧ Y x = 0) : EqOn v 0 Ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.Conformal.ClosedDiskChart` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.InInteriorNeumannEigenspace` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.AdmissibleDomain` and `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.closedTraceSpace_local_rank` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Cauchy.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.eq_zero_of_boundary_closedGradient)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedEigenLocalRank

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots
namespace Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c

theorem eq_zero_of_boundary_closedGradient (hΩ : AdmissibleDomain Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v)
    (hvc : ContinuousOn v (closure Ω)) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    {p : Plane} (hp : p ∈ frontier Ω) {U : Set Plane} (hU : IsOpen U) (hpU : p ∈ U)
    (hz : ∀ x ∈ U ∩ frontier Ω, v x = 0 ∧ Y x = 0) : EqOn v 0 Ω := by
  sorry
end Conformal.ClosedDiskChart

end StrictHotSpots
end
end ClosedEigenLocalRank

end OAI
end
