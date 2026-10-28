-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_Hodge_vector_equality_interior_pointwise
-- name    : OAI.StrictHotSpots.Hodge.vector_equality_interior_pointwise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:17:57.05626+00:00
-- url     : https://prove2.me/theorems/697eb516-7d13-4d42-8c71-e7f9143bdbe8
-- title:
--   OAI.StrictHotSpots.Hodge.vector_equality_interior_pointwise: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.Hodge.vector_equality_interior_pointwise` of [lean/OAI/Analysis/HotSpots/HotSpots/Eigenfunction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Eigenfunction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.Hodge`, with `open Set MeasureTheory Filter Metric`, `open scoped ContDiff Laplacian Topology`, `open Set MeasureTheory Filter`, `open scoped ContDiff InnerProductSpace Topology`):
--
--   ```lean
--   theorem vector_equality_interior_pointwise {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
--       (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
--       (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
--       (hl : firstPositiveNeumannValue Ω < L)
--       (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
--       (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
--       (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G)
--       (hE : firstPositiveNeumannValue Ω * ‖X‖^2 = ‖F‖^2+‖G‖^2)
--       (Y : Plane → Plane) (hY : ContinuousOn Y Ω) (ha : X =ᵐ[volume.restrict Ω] Y) :
--       ∃ v : Plane → ℝ, InInteriorNeumannEigenspace Ω v ∧ EqOn (gradient v) Y Ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.H10.grad` and `OAI.StrictHotSpots.H10.value` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.InInteriorNeumannEigenspace`, `OAI.StrictHotSpots.Hodge.V2` and `OAI.StrictHotSpots.Hodge.WeakNormalDiv` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Hodge.WeakCurl` (definitions bundle `OAIQ3Ho004` of this split); `OAI.StrictHotSpots.Plane` and `OAI.StrictHotSpots.firstPositiveNeumannValue` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.Conformal.ClosedDiskChart.coordinate_null_trace` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/Eigenfunction.lean (declaration OAI.StrictHotSpots.Hodge.vector_equality_interior_pointwise)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorEigenSupport

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian Topology

section HodgeInteriorNullspaceActualInteriorLayer
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots.Hodge

theorem vector_equality_interior_pointwise {Ω : Set Plane} (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hs : IsSimplyConnected Ω) (hb : Bornology.IsBounded Ω)
    (hμ : 0 < firstPositiveNeumannValue Ω) {L : ℝ}
    (hl : firstPositiveNeumannValue Ω < L)
    (hD : ∀ j : H10 ho, L*‖H10.value ho j‖^2 ≤ ‖H10.grad ho j‖^2)
    (X : V2 Ω) (F G : Lp ℝ 2 (volume.restrict Ω))
    (hF : WeakNormalDiv X F) (hG : WeakCurl ho X G)
    (hE : firstPositiveNeumannValue Ω * ‖X‖^2 = ‖F‖^2+‖G‖^2)
    (Y : Plane → Plane) (hY : ContinuousOn Y Ω) (ha : X =ᵐ[volume.restrict Ω] Y) :
    ∃ v : Plane → ℝ, InInteriorNeumannEigenspace Ω v ∧ EqOn (gradient v) Y Ω := by
  sorry

end StrictHotSpots.Hodge
end
end HodgeInteriorNullspaceActualInteriorLayer
end
end ActualInteriorEigenSupport

end OAI
end
