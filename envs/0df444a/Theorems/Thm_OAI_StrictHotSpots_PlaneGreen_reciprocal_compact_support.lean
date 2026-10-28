-- Prove2me | Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_reciprocal_compact_support
-- name    : OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T05:15:00.975424+00:00
-- url     : https://prove2.me/theorems/9d2331e6-3104-4d66-947b-f96245707991
-- title:
--   OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support: intermediate lemma from OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support` of [lean/OAI/Analysis/HotSpots/HotSpots/BoundaryKernel.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/BoundaryKernel.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.StrictHotSpots.PlaneGreen`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology InnerProductSpace`, `open DiskH10`):
--
--   ```lean
--   theorem reciprocal_compact_support (K : Set Plane) (hK : IsCompact K) (hKd : K ⊆ disk)
--       (hsupp : ν Kᶜ = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
--       (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
--         d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → disk) :
--       ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
--         (resolved hC hν (s i) (s j))⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ReciprocalKernel.OnePositiveSquare`, `OAI.StrictHotSpots.H1`, `OAI.StrictHotSpots.H10`, `OAI.StrictHotSpots.H1Ambient`, `OAI.StrictHotSpots.DiskH10.disk`, `OAI.StrictHotSpots.H10.grad` and `OAI.StrictHotSpots.PlaneGreen.diskOpen` (definitions bundle `OAIQ3Ho000` of this split); `OAI.StrictHotSpots.H10.weightedValue` (definitions bundle `OAIQ3Ho002` of this split); `OAI.StrictHotSpots.PlaneGreen.resolved` (definitions bundle `OAIQ3Ho003` of this split); `OAI.StrictHotSpots.Plane` (the published bundle `Def_HotSpots`).
--
--   **Used by.** The proof of `OAI.StrictHotSpots.PlaneGreen.full_boundary_hilbert_embedding` of this split imports it.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/HotSpots/HotSpots/BoundaryKernel.lean (declaration OAI.StrictHotSpots.PlaneGreen.reciprocal_compact_support)

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
import Definitions.Def_OAIQ3Ho003

section

attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section PlaneCompactSupportLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable (ν : Measure Plane) [IsFiniteMeasure ν] {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

theorem reciprocal_compact_support (K : Set Plane) (hK : IsCompact K) (hKd : K ⊆ disk)
    (hsupp : ν Kᶜ = 0) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hsub : ∀ u : H10 diskOpen, ‖H10.weightedValue diskOpen hC hν u‖ ^ 2 ≤
      d * ‖H10.grad diskOpen u‖ ^ 2) {ι : Type} [Fintype ι] (s : ι → disk) :
    ReciprocalKernel.OnePositiveSquare (Matrix.of fun i j => if s i = s j then 0 else
      (resolved hC hν (s i) (s j))⁻¹) := by
  sorry

end StrictHotSpots.PlaneGreen
end
end PlaneCompactSupportLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end
