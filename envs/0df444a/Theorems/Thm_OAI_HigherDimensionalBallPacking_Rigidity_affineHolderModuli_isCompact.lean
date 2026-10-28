-- Prove2me | Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_affineHolderModuli_isCompact
-- name    : OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T16:39:50.180975+00:00
-- url     : https://prove2.me/theorems/a411b6f1-b10a-450b-9bb5-c9478e300b94
-- title:
--   OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.packing_necessity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact` of [lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HigherDimensionalBallPacking.Rigidity`, with `open scoped ContDiff Topology`, `open Set Function Filter`, `open scoped ContDiff Topology Manifold`, `open Set Function Filter MeasureTheory`, `open Set Function MeasureTheory`, `open Set Function`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)`, `open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)`, `open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)`, `open SymplecticBallPacking.Hamiltonian`, `open SymplecticBallPacking.Hamiltonian (Plane)`, `open Set Filter Function`, `open Set Filter MeasureTheory`, `open scoped Topology`, `open Set Filter Finset`, `open scoped ContDiff Topology Classical`, `open Set Filter`, `open scoped BoundedContinuousFunction ContDiff Topology`, `open Set Function Filter Topology`, `open scoped NNReal`, `open scoped ContDiff Topology BoundedContinuousFunction`, `open Function`, `open scoped Topology ContDiff`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open scoped ContDiff Topology`, `open Set Filter Function`, `open HigherDimensionalBallPacking.Rigidity`, `open FramedCR`):
--
--   ```lean
--   theorem affineHolderModuli_isCompact (n : ℕ) (hn : 3 ≤ n)
--       (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
--       (hJ : ∀ x, Compatible (J x))
--       (hc : HasCompactSupport (fun x => J x-standardJ n))
--       (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
--       (p q : Phase n) (hpq : p ≠ q) (R : ℝ)
--       (hR : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
--         AffineLineCurve (lineHomotopy J t) p q u →
--         ∀ z, R < ‖z‖ → standardCurl u z=0) :
--       IsCompact (affineHolderModuli J p q R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HigherDimensionalBallPacking.Rigidity.CompactHolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.Compatible`, `OAI.HigherDimensionalBallPacking.Rigidity.End`, `OAI.HigherDimensionalBallPacking.Rigidity.HolderSpace`, `OAI.HigherDimensionalBallPacking.Rigidity.OffDiagonal`, `OAI.HigherDimensionalBallPacking.Rigidity.compactHolderSubmodule`, `OAI.HigherDimensionalBallPacking.Rigidity.holderGraph` and `OAI.HigherDimensionalBallPacking.Rigidity.standardJ` (definitions bundle `OAIQ10Bp000` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.FramedCR.standardCurl` (definitions bundle `OAIQ10Bp001` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.AffineLineCurve` (definitions bundle `OAIQ10Bp002` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.lineHomotopy` (definitions bundle `OAIQ10Bp003` of this split); `OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli` (definitions bundle `OAIQ10Bp005` of this split); `OAI.HigherDimensionalBallPacking.Phase` and `OAI.HigherDimensionalBallPacking.openBall` (the published bundle `Def_BallPackingNecessity`).
--
--   **Used by.** The proofs of `OAI_HigherDimensionalBallPacking_Rigidity_actual_affine_line_exists`, `OAI.HigherDimensionalBallPacking.Rigidity.homotopy_affine_Holder_compactness` and `OAI.HigherDimensionalBallPacking.normalized_two_ball_obstruction` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallPacking/Necessity/DensityLimits.lean (declaration OAI.HigherDimensionalBallPacking.Rigidity.affineHolderModuli_isCompact)

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

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Filter Function
section
open HigherDimensionalBallPacking.Rigidity
open FramedCR

theorem affineHolderModuli_isCompact (n : ℕ) (hn : 3 ≤ n)
    (J : Phase n → End n) (hJs : ContDiff ℝ ∞ J)
    (hJ : ∀ x, Compatible (J x))
    (hc : HasCompactSupport (fun x => J x-standardJ n))
    (hs : tsupport (fun x => J x-standardJ n) ⊆ openBall n 1)
    (p q : Phase n) (hpq : p ≠ q) (R : ℝ)
    (hR : ∀ t ∈ Icc (0:ℝ) 1, ∀ u : ℂ → Phase n,
      AffineLineCurve (lineHomotopy J t) p q u →
      ∀ z, R < ‖z‖ → standardCurl u z=0) :
    IsCompact (affineHolderModuli J p q R) := by
  sorry

end

open scoped ContDiff Topology
open Set Filter Function

open scoped ContDiff Topology
open Set Filter Function

end HigherDimensionalBallPacking.Rigidity

end

end OAI
end
