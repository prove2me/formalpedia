-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_normalCoupling_invertible_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCoupling_invertible_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:30.260674+00:00
-- url     : https://prove2.me/theorems/a861585f-e5b2-46a0-ad1c-fc1b9e81f8a8
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCoupling_invertible_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCoupling_invertible` of [lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open Hamiltonian`, `open scoped BigOperators`):
--
--   ```lean
--   theorem normalCoupling_invertible_bp240 {d : ℝ} (hd : d<1/2) {x : NormalSpace a}
--       (hx : Real.pi*phaseSq x.2≤d) :
--       (manifoldExteriorOneForm (normalCouplingPrimitive a) x).IsInvertible
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.NormalSpace` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCouplingPrimitive` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.HigherDimensionalBallPacking.main_theorem` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.normalCoupling_invertible)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Hamiltonian
open scoped BigOperators
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem normalCoupling_invertible_bp240 {d : ℝ} (hd : d<1/2) {x : NormalSpace a}
    (hx : Real.pi*phaseSq x.2≤d) :
    (manifoldExteriorOneForm (normalCouplingPrimitive a) x).IsInvertible := by
  sorry

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
