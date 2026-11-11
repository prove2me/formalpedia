-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_largeCouplingPrimitive_invertible_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive_invertible_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:53:29.837364+00:00
-- url     : https://prove2.me/theorems/6b85c3c9-81f0-4ea1-8248-78f7b38a4777
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive_invertible_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive_invertible` of [lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Manifold`, `open Hamiltonian`, `open scoped BigOperators`):
--
--   ```lean
--    theorem largeCouplingPrimitive_invertible_bp240 {x : LargeNormalSpace a}
--       (hx : 0<1-radialArea (normalHead m x.2)-2*Real.pi*phaseSq (normalTail m x.2)) :
--       (manifoldExteriorOneForm (largeCouplingPrimitive a) x).IsInvertible
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.phaseSq` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.radialArea` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.LargeNormalModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.LargeNormalSpace`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive`, `OAI.PackingSufficiencySupport.Hamiltonian.normalHead` and `OAI.PackingSufficiencySupport.Hamiltonian.normalTail` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.actual_complement_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/QuadricMovingCone.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.largeCouplingPrimitive_invertible)

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

 theorem largeCouplingPrimitive_invertible_bp240 {x : LargeNormalSpace a}
    (hx : 0<1-radialArea (normalHead m x.2)-2*Real.pi*phaseSq (normalTail m x.2)) :
    (manifoldExteriorOneForm (largeCouplingPrimitive a) x).IsInvertible := by
  sorry

end

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
