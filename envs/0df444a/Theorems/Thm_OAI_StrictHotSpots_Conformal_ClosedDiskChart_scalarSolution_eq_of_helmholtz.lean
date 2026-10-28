-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_eq_of_helmholtz
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:17:49.04602+00:00
-- url     : https://prove2.me/theorems/098584ab-19e6-48de-a26a-9f968a81346e
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz` of [lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace ENNReal NNReal Laplacian`, `open DiskH10 PlaneGreen Hodge`):
--
--   ```lean
--   lemma scalarSolution_eq_of_helmholtz (hne : Ω.Nonempty)
--       {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
--       (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) :
--       c.scalarSolution hb hs hμ hw = (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.HasH1Gradient.toH1` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.diskMap` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.smooth_closure_H1` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.Plane`, `OAI.StrictHotSpots.SmoothBoundary` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Laplacian
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

lemma scalarSolution_eq_of_helmholtz (hne : Ω.Nonempty)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hp : ∀ x ∈ Ω, Δ w x = -firstPositiveNeumannValue Ω*w x) :
    c.scalarSolution hb hs hμ hw = (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw).toH1 := by
  sorry

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualVectorEnergy

end OAI
end
