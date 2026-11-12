-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialOrbit_initialShapeCode_eq_iff
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:15.478207+00:00
-- url     : https://prove2.me/theorems/883effd4-b337-4c83-87ea-70f9765f748b
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff` of [lean/OAI/LinearAlgebra/MatrixFields/Histories/InitialOrbit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Histories/InitialOrbit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldInitialEntropy`, `open scoped BigOperators`):
--
--   ```lean
--   theorem initialShapeCode_eq_iff (p : PlacedInitial) (u : JointPopulation.Shape) :
--       initialShapeCode p = u ↔
--         physicalShape p.2 (sortedInitial.get p.1) = decodeShape u
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.decodeShape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.PlacedInitial`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.initialShapeCode`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.sortedInitial` and `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldScheduledPositivity.nativeH0_pos` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Histories/InitialOrbit.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.initialShapeCode_eq_iff)

import Mathlib
import Definitions.Def_OAIQ254M000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldInitialOrbit

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy
open scoped BigOperators

theorem initialShapeCode_eq_iff (p : PlacedInitial) (u : JointPopulation.Shape) :
    initialShapeCode p = u ↔
      physicalShape p.2 (sortedInitial.get p.1) = decodeShape u := by
  sorry

end MatrixMultiplication.AllFieldInitialOrbit

end MatrixAllFields

end OAI
end
