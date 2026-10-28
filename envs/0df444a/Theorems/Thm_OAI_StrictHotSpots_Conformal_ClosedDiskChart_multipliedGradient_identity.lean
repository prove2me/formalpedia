-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_multipliedGradient_identity
-- name    : OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:16:14.950422+00:00
-- url     : https://prove2.me/theorems/099d8f1d-6c29-45bf-b7dd-3bbcb7a38abb
-- title:
--   OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_identity: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_identity` of [lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, with `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace ENNReal NNReal`, `open DiskH10 PlaneGreen Hodge`):
--
--   ```lean
--   theorem multipliedGradient_identity {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
--       (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
--       vectorForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
--         (c.multipliedGradient hΩ hu hμ hb) =
--       cartesianForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
--         (c.multipliedGradient hΩ hu hμ hb)-
--       cartesianForm (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
--         (c.multipliedGradient hΩ hu hμ (hb.mul hb))
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.Conformal.ClosedDiskChart` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.Hodge.eigenGradientField` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.Hodge.cartesianForm` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Hodge.vectorForm` and `OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.AdmissibleDomain`, `OAI.StrictHotSpots.InFirstNeumannEigenspace`, `OAI.StrictHotSpots.Plane` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/VectorEnergy.lean (declaration OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_identity)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section SmoothPhysicalMultiplier

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

theorem multipliedGradient_identity {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    vectorForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb) =
    cartesianForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb)-
    cartesianForm (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu)
      (c.multipliedGradient hΩ hu hμ (hb.mul hb)) := by
  sorry

end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothPhysicalMultiplier

end OAI
end
