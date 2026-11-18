-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularPower_positive
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T19:00:58.186273+00:00
-- url     : https://prove2.me/theorems/10049895-9439-4810-a65b-a5fdb961a471
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularPositivePowers.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularPositivePowers.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma triangularPower_positive (N:ℕ)
--       (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
--       IntegralPositive (extendedOmega n)
--         (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
--           (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (linearPower N))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.PowerSeriesAdjoint.adjoint`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.chartCompletionAddGroup`, `OAI.ElementaryPositivity.QuantumTorus.homogenize`, `OAI.ElementaryPositivity.QuantumTorus.rootGrade`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instOne`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.rootOrder` (definitions bundle `OAIQ368Chrom002` of this split); `OAI.ElementaryPositivity.QuantumTorus.rootSectionChart` (definitions bundle `OAIQ368Chrom012` of this split); `OAI.ElementaryPositivity.QuantumTorus.IntegralPositive` (definitions bundle `OAIQ368Chrom013` of this split); `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.GapIndex` and `OAI.ElementaryPositivity.TriangularDynamics.Vertex` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeRealization.extendedCast`, `OAI.ElementaryPositivity.TriangularDynamics.extendedCoord`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.extendedRoots`, `OAI.ElementaryPositivity.TriangularDynamics.linearPower`, `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` and `OAI.ElementaryPositivity.TriangularDynamics.triangularPositivePowersRing` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_incoming_retain` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularPositivePowers.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive)

import Mathlib
import Definitions.Def_OAIQ368Chrom058

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint LaurentPositive
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

attribute [local instance] OAI.ElementaryPositivity.TriangularDynamics.triangularPositivePowersRing
local instance triangularPositivePowersAddCommMonoid_r87d959_1 : AddCommMonoid (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommMonoid
local instance triangularPositivePowersAddCommGroup_r87d959_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularPositivePowersAddGroup_r87d959_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
lemma triangularPower_positive (N:ℕ)
    (h:Module.Dual ℝ ((Vertex n (Cell n) → ℝ) × (Vertex n (Cell n) → ℝ))) :
    IntegralPositive (extendedOmega n)
      (adjoint (rootSectionChart (extendedOmega n) (extendedRoots n) (h.toAddMonoidHom.comp extendedCast)).val
        (homogenize LaurentRay.vUnit (extendedOmega n) (rootOrder (extendedCoord n)) (triangularExpression (linearPower N)))) := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
