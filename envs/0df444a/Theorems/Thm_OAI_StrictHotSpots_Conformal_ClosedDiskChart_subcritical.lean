-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_subcritical
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:07:10.480971+00:00
-- url     : https://prove2.me/theorems/2802c137-fc7e-4532-be41-e9887ab39f02
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical` of [lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ENNReal InnerProductSpace`, `open DiskH10`):
--
--   ```lean
--   theorem subcritical (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
--       (hμ : 0 < firstPositiveNeumannValue Ω) :
--       ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ v : H10 PlaneGreen.diskOpen,
--         ‖H10.weightedValue PlaneGreen.diskOpen c.densityBound_ne_top (c.density_bound hμ.le) v‖^2 ≤
--           δ*‖H10.grad PlaneGreen.diskOpen v‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.H10.grad`, `OAI.StrictHotSpots.PlaneGreen.diskOpen`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound_ne_top`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.density_bound` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.H10.weightedValue` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.Plane` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proofs of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.gradient_K_representation`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.operator_norm_lt_one`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.scalarSolution_eq_of_helmholtz` and `OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_form` of this split import it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Pullback.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.subcritical)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002

section

attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualPotential

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.Conformal
open DiskH10

namespace ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

theorem subcritical (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (hμ : 0 < firstPositiveNeumannValue Ω) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ v : H10 PlaneGreen.diskOpen,
      ‖H10.weightedValue PlaneGreen.diskOpen c.densityBound_ne_top (c.density_bound hμ.le) v‖^2 ≤
        δ*‖H10.grad PlaneGreen.diskOpen v‖^2 := by
  sorry

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualPotential

end OAI
end
