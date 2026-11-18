-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_locality
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T19:00:42.466119+00:00
-- url     : https://prove2.me/theorems/d3d68a37-3ebc-44c3-bbf8-4ef2a13271fb
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearIncoming.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearIncoming.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma triangularLinear_locality (m:Lattice n (Cell n)) (hm:triangularIncoming (.atom 1) m≠0) :
--       triangularIncoming (.atom 1) m=triangularExpression (.atom 1) (includeVertices m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.Torus` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.Lattice`, `OAI.ElementaryPositivity.TriangularDynamics.Vertex` and `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeExtension.includeVertices`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` and `OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearIncoming.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_locality)

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
open QuantumTorus WallUnits LatticeExtension
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ}

lemma triangularLinear_locality (m:Lattice n (Cell n)) (hm:triangularIncoming (.atom 1) m≠0) :
    triangularIncoming (.atom 1) m=triangularExpression (.atom 1) (includeVertices m) := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
