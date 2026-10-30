-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_orbit_regular
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:45.491322+00:00
-- url     : https://prove2.me/theorems/a702a311-ff86-4299-8cf5-292f935e28ff
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)`, `open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)`, `open SymplecticBallPacking.Hamiltonian`, `open SymplecticBallPacking.Hamiltonian (Plane)`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology Convolution`, `open Set Filter Function MeasureTheory _root_.ContinuousLinearMap`, `open Set Filter Function MeasureTheory`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`):
--
--   ```lean
--   theorem c1_orbit_regular (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α)
--       (U : Set ℂ) (hU : IsOpen U) (h0 : (0:ℂ)∈U)
--       (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
--       (hΦ : ∀ h∈U, ContDiffAt ℝ ∞ Φ (h,holderShift α h (c1HolderValue α f)))
--       (heq : ∀ h∈U, c1HolderShift α h f=Φ (h,holderShift α h (c1HolderValue α f))) :
--       ContDiff ℝ ∞ (holderValue α (c1HolderValue α f))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.C1HolderAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.C1HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.OffDiagonal`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderValue`, `OAI.HigherDimensionalBallPacking.Rigidity.holderGraph` and `OAI.HigherDimensionalBallPacking.Rigidity.holderValue` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderShift` and `OAI.HigherDimensionalBallPacking.Rigidity.holderShift` (definitions bundle `OAIQ10Bp004` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Group`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Space`, `OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderGroup` and `OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderSpace` (definitions bundle `OAIQ10Bp008` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_regular)

import Mathlib
import Definitions.Def_OAIQ10Bp004
import Definitions.Def_OAIQ10Bp008

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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Group
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Space
theorem c1_orbit_regular (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α)
    (U : Set ℂ) (hU : IsOpen U) (h0 : (0:ℂ)∈U)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ∀ h∈U, ContDiffAt ℝ ∞ Φ (h,holderShift α h (c1HolderValue α f)))
    (heq : ∀ h∈U, c1HolderShift α h f=Φ (h,holderShift α h (c1HolderValue α f))) :
    ContDiff ℝ ∞ (holderValue α (c1HolderValue α f)) := by
  sorry

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end
