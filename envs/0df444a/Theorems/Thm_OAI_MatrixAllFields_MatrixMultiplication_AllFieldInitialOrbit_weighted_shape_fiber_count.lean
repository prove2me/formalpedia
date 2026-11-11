-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialOrbit_weighted_shape_fiber_count
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T05:48:28.989377+00:00
-- url     : https://prove2.me/theorems/95f3c368-5dfb-42b5-903a-b7187e930d59
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count` of [lean/OAI/LinearAlgebra/MatrixFields/Histories/InitialOrbit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Histories/InitialOrbit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldParameters AllFieldHistory AllFieldInitialEntropy`, `open scoped BigOperators`):
--
--   ```lean
--   theorem weighted_shape_fiber_count : ∀ u ∈ shapes 16,
--       (∑ p : PlacedInitial,
--         if physicalShape p.2 (sortedInitial.get p.1) = u
--         then initialMultiplicity (sortedInitial.get p.1) else 0) = 6
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.physicalShape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropy.PlacedInitial`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.initialMultiplicity`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.shapes` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.sortedInitial` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialChoice.eventually_nonempty` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Histories/InitialOrbit.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialOrbit.weighted_shape_fiber_count)

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

theorem weighted_shape_fiber_count : ∀ u ∈ shapes 16,
    (∑ p : PlacedInitial,
      if physicalShape p.2 (sortedInitial.get p.1) = u
      then initialMultiplicity (sortedInitial.get p.1) else 0) = 6 := by
  sorry

end MatrixMultiplication.AllFieldInitialOrbit

end MatrixAllFields

end OAI
end
