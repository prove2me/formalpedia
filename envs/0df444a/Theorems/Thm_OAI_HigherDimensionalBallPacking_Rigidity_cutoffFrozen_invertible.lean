-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_cutoffFrozen_invertible
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:53:58.796462+00:00
-- url     : https://prove2.me/theorems/3a25b617-912a-4851-a83e-7a850afab823
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenResponse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenResponse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)`, `open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)`, `open SymplecticBallPacking.Hamiltonian`, `open SymplecticBallPacking.Hamiltonian (Plane)`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology Convolution`, `open Set Filter Function MeasureTheory _root_.ContinuousLinearMap`, `open Set Filter Function MeasureTheory`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open HigherDimensionalBallPacking.Rigidity`):
--
--   ```lean
--    theorem cutoffFrozen_invertible {n : ℕ} (b : ContDiffBump (0:ℂ))
--       (H : C1HolderSpace (End n) ((1:ℝ)/3))
--       (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z=0)
--       (hK : ∀ z, Compatible (standardJ n+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z)) :
--       (cutoffFrozen b (c1HolderValue ((1:ℝ)/3) H)).IsInvertible
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.C1HolderAmbient`, `OAI.HigherDimensionalBallPacking.Rigidity.C1HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.CompactHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.OffDiagonal`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderGraph`, `OAI.HigherDimensionalBallPacking.Rigidity.c1HolderValue`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule`, `OAI.HigherDimensionalBallPacking.Rigidity.holderGraph`, `OAI.HigherDimensionalBallPacking.Rigidity.holderValue` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen` (definitions bundle `OAIQ10Bp007` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proofs of `OAI_HigherDimensionalBallPacking_Rigidity_actual_affine_line_exists`, `OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular` and `OAI.HigherDimensionalBallPacking.Rigidity.responseCoefficient_invertible` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/FrozenResponse.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen_invertible)

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007

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
open HigherDimensionalBallPacking.Rigidity

 theorem cutoffFrozen_invertible {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : C1HolderSpace (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z=0)
    (hK : ∀ z, Compatible (standardJ n+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z)) :
    (cutoffFrozen b (c1HolderValue ((1:ℝ)/3) H)).IsInvertible := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
