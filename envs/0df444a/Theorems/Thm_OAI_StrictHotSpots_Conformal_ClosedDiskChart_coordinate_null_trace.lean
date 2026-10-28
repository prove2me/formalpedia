-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_coordinate_null_trace
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:08:22.219821+00:00
-- url     : https://prove2.me/theorems/b0c5d8aa-567b-4e2a-a561-8844000b01f6
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace` of [lean/OAI/Analysis/HotSpots/HotSpots/Eigenfunction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Eigenfunction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter Metric Function`, `open scoped ENNReal NNReal Topology InnerProductSpace`, `open PlaneGreen DiskH10 Hodge HilbertMultipliers`):
--
--   ```lean
--   theorem coordinate_null_trace (hΩ : AdmissibleDomain Ω)
--       {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
--       (p : disk) (hz : gradient u (c.F p) = 0) [IsFiniteMeasure c.potential]
--       {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Countable ι]
--       (e : HilbertBasis ι ℝ H) {b : Boundary → H} {B : ℝ≥0} (hb : LipschitzWith B b)
--       (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel c.densityBound_ne_top
--         (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s t) :
--       ∀ i, ∃ (v : Plane → ℝ) (Y : Plane → Plane), InInteriorNeumannEigenspace Ω v ∧
--         ContinuousOn v (closure Ω) ∧ ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧
--         ∀ s : Boundary, Y (c.F s) = inner ℝ (e i) (b s) • closedGradient Ω u (c.F s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.closedGradient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.PlaneGreen.Boundary`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.InInteriorNeumannEigenspace`, `OAI.StrictHotSpots.firstPositiveNeumannValue_pos_of_eigenfunction` and `OAI.StrictHotSpots.PlaneGreen.fullDistanceKernel` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace`, `OAI.StrictHotSpots.Plane` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Eigenfunction.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalCoordinateNull

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
open PlaneGreen DiskH10 Hodge HilbertMultipliers
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

theorem coordinate_null_trace (hΩ : AdmissibleDomain Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (hne : ∃ x ∈ Ω, u x ≠ 0)
    (p : disk) (hz : gradient u (c.F p) = 0) [IsFiniteMeasure c.potential]
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Countable ι]
    (e : HilbertBasis ι ℝ H) {b : Boundary → H} {B : ℝ≥0} (hb : LipschitzWith B b)
    (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel c.densityBound_ne_top
      (c.density_bound (firstPositiveNeumannValue_pos_of_eigenfunction hΩ hu hne).le) p s t) :
    ∀ i, ∃ (v : Plane → ℝ) (Y : Plane → Plane), InInteriorNeumannEigenspace Ω v ∧
      ContinuousOn v (closure Ω) ∧ ContinuousOn Y (closure Ω) ∧ EqOn (gradient v) Y Ω ∧
      ∀ s : Boundary, Y (c.F s) = inner ℝ (e i) (b s) • closedGradient Ω u (c.F s) := by
  sorry
end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalCoordinateNull

end OAI
end
