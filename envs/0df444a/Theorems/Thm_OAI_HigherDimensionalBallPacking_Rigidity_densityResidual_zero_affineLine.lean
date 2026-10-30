-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_densityResidual_zero_affineLine
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:43:24.393128+00:00
-- url     : https://prove2.me/theorems/c1362665-1d60-430d-9221-183a517d428b
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityMaps.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityMaps.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)`, `open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)`, `open SymplecticBallPacking.Hamiltonian`, `open SymplecticBallPacking.Hamiltonian (Plane)`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology Convolution`, `open Set Filter Function MeasureTheory _root_.ContinuousLinearMap`, `open Set Filter Function MeasureTheory`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open HigherDimensionalBallPacking.Rigidity FramedCR`):
--
--   ```lean
--    theorem densityResidual_zero_affineLine {n : ℕ} (p q : Phase n) (R : ℝ)
--       (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
--       (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
--       (hJ : ∀ x, Compatible (J x)) (hJc : HasCompactSupport (fun x => J x-standardJ n))
--       (he : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
--       (y : ℝ × CompactHolderSpace (Phase n) R) (hy : y.1∈Icc (0:ℝ) 1)
--       (ha : densitySlope p q R y.2≠0) (hz : densityResidual p q R A hA hc y=0) :
--       AffineLineCurve (lineHomotopy J y.1) p q (densityCurve p q R y.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.CompactHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.OffDiagonal`, `OAI.HigherDimensionalBallPacking.Rigidity.holderGraph` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve` (definitions bundle `OAIQ10Bp002` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy` (definitions bundle `OAIQ10Bp003` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.densityCurve`, `OAI.HigherDimensionalBallPacking.Rigidity.densityResidual` and `OAI.HigherDimensionalBallPacking.Rigidity.densitySlope` (definitions bundle `OAIQ10Bp005` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proofs of `OAI_HigherDimensionalBallPacking_Rigidity_actual_affine_line_exists` and `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityMaps.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.densityResidual_zero_affineLine)

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity FramedCR

 theorem densityResidual_zero_affineLine {n : ℕ} (p q : Phase n) (R : ℝ)
    (A : ℝ × Phase n → End n) (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport A)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x)) (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (he : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, A (t,x)=lineHomotopy J t x-standardJ n)
    (y : ℝ × CompactHolderSpace (Phase n) R) (hy : y.1∈Icc (0:ℝ) 1)
    (ha : densitySlope p q R y.2≠0) (hz : densityResidual p q R A hA hc y=0) :
    AffineLineCurve (lineHomotopy J y.1) p q (densityCurve p q R y.2) := by
  sorry

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end
