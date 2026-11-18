-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularPure_equal
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:37:03.127486+00:00
-- url     : https://prove2.me/theorems/fe882be8-dcc8-4527-bc8b-bd94db44a0b3
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension`, `open Classical`):
--
--   ```lean
--   lemma triangularPure_equal {N:ℕ} (f g:ElementaryExpr N)
--       (hp:∀μ:Fin (n+1) → ℤ,triangularExpression f (includeVertices (pureAnchor μ))=
--           triangularExpression g (includeVertices (pureAnchor μ))) :
--       triangularExpression (n:=n) f=triangularExpression g
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.QuantumTorus.Torus` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr`, `OAI.ElementaryPositivity.TriangularDynamics.Cell` and `OAI.ElementaryPositivity.TriangularDynamics.Vertex` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.LatticeExtension.Extended`, `OAI.ElementaryPositivity.LatticeExtension.includeVertices`, `OAI.ElementaryPositivity.TriangularDynamics.extendedOmega`, `OAI.ElementaryPositivity.TriangularDynamics.pureAnchor` and `OAI.ElementaryPositivity.TriangularDynamics.triangularExpression` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history` and `OAI_ElementaryPositivity_TriangularDynamics_triangularExpression_anchorSupported` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularCommutativity.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal)

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
open Classical
noncomputable section
variable {n:ℕ}

local instance triangularCommutativityRing_r459811_1 : Ring (Torus LaurentRay.vUnit (extendedOmega n)) := Torus.instRing LaurentRay.vUnit (extendedOmega n)
local instance triangularCommutativityAddCommGroup_r459811_1 : AddCommGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddCommGroup
local instance triangularCommutativityAddGroup_r459811_1 : AddGroup (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toAddGroup
local instance triangularCommutativitySub_r459811_1 : Sub (Torus LaurentRay.vUnit (extendedOmega n)) := (Torus.instRing LaurentRay.vUnit (extendedOmega n)).toSub
lemma triangularPure_equal {N:ℕ} (f g:ElementaryExpr N)
    (hp:∀μ:Fin (n+1) → ℤ,triangularExpression f (includeVertices (pureAnchor μ))=
        triangularExpression g (includeVertices (pureAnchor μ))) :
    triangularExpression (n:=n) f=triangularExpression g := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
