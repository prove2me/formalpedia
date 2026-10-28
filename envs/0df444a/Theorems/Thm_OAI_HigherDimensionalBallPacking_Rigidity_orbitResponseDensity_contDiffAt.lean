-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_orbitResponseDensity_contDiffAt
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:52:20.968628+00:00
-- url     : https://prove2.me/theorems/100b4f3c-718a-41f4-b9b0-dd8ed02510dc
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)`, `open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)`, `open SymplecticBallPacking.Hamiltonian`, `open SymplecticBallPacking.Hamiltonian (Plane)`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology Convolution`, `open Set Filter Function MeasureTheory _root_.ContinuousLinearMap`, `open Set Filter Function MeasureTheory`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Set Filter Function`, `open HigherDimensionalBallPacking.Rigidity`):
--
--   ```lean
--   theorem orbitResponseDensity_contDiffAt {n : ℕ} (b : ContDiffBump (0:ℂ))
--       (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n) (ha : a≠0)
--       (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3))
--       (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a p)).IsInvertible) :
--       ContDiffAt ℝ ∞ (fun p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3) =>
--         frozenResponse b (orbitCoefficient f hf hc c a p,a)) p
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.CompactHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.OffDiagonal`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule` and `OAI.HigherDimensionalBallPacking.Rigidity.holderGraph` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal1` and `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal2` (definitions bundle `OAIQ10Bp004` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal7`, `OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal8`, `OAI.HigherDimensionalBallPacking.Rigidity.cutoffFrozen` and `OAI.HigherDimensionalBallPacking.Rigidity.frozenResponse` (definitions bundle `OAIQ10Bp007` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.orbitCoefficient` (definitions bundle `OAIQ10Bp008` of this split); `OAI.HigherDimensionalBallPacking.Phase` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.Rigidity.affine_c1_regular` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/OrbitRegularity.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.orbitResponseDensity_contDiffAt)

import Mathlib
import Definitions.Def_BallPackingNecessity
import Definitions.Def_OAIQ10Bp007
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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularHSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.regularCompactSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal1
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal2
local instance AffineC1RegularityLocal3_r1443e8_1 (n : ℕ) : NormedAddCommGroup (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
local instance AffineC1RegularityLocal4_r1443e8_1 (n : ℕ) : NormedSpace ℝ (HolderSpace ℂ (End n) ((1:ℝ)/3)) := inferInstance
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal7
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.AffineC1RegularityLocal8
theorem orbitResponseDensity_contDiffAt {n : ℕ} (b : ContDiffBump (0:ℂ))
    (f : Phase n → End n) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (c a : Phase n) (ha : a≠0)
    (p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3))
    (hi : (cutoffFrozen b (orbitCoefficient f hf hc c a p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun p : ℂ × HolderSpace ℂ (Phase n) ((1:ℝ)/3) =>
      frozenResponse b (orbitCoefficient f hf hc c a p,a)) p := by
  sorry

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
