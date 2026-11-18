-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_triangularLinear_anchorIncoming
-- name    : OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T19:00:58.487282+00:00
-- url     : https://prove2.me/theorems/1483bef8-6376-48ca-9f23-79698d09b77b
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming` of [lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearIncoming.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearIncoming.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension`, `open scoped BigOperators`, `open Classical`):
--
--   ```lean
--   lemma triangularLinear_anchorIncoming : triangularIncoming (n:=n) (.atom 1) (anchor 0)=1
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.TriangularDynamics.Cell`, `OAI.ElementaryPositivity.TriangularDynamics.anchor` and `OAI.ElementaryPositivity.QuantumTorus.ElementaryExpr` (definitions bundle `OAIQ368Chrom057` of this split); `OAI.ElementaryPositivity.TriangularDynamics.triangularIncoming` (definitions bundle `OAIQ368Chrom058` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.TriangularDynamics.triangularPower_positive` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Walls/TriangularLinearIncoming.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.triangularLinear_anchorIncoming)

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

lemma triangularLinear_anchorIncoming : triangularIncoming (n:=n) (.atom 1) (anchor 0)=1 := by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
