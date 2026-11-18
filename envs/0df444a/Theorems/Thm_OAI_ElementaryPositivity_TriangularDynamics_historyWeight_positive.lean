-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_historyWeight_positive
-- name    : OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T20:13:50.140202+00:00
-- url     : https://prove2.me/theorems/b2a573ad-62a0-4e41-9ed7-177e560c8588
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive` of [lean/OAI/Combinatorics/Chromatic/Witness/ElementarySingletonCoefficient.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementarySingletonCoefficient.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization`, `open scoped BigOperators`, `open Classical`, and `variable {n:ℕ} (G:NaturalUnitIntervalGraph n)`):
--
--   ```lean
--   lemma historyWeight_positive (l:HistoryLeaf G) : LaurentPositive.Positive (historyWeight G l)
--   ```
--
--   **In words.** For every leaf `l` of `HistoryLeaf G`, the statement says that the Laurent series `historyWeight G l` is `LaurentPositive.Positive`.
--
--   **Definitions.** The statement uses `HistoryLeaf`, `historyWeight` and `LaurentPositive.Positive`, written in the definitions bundle `OAIQ368Chrom059` of this split and in the shared definitions file Def_ElementaryPositivity.
--
--   **Used by.** The proof file of `OAI.ElementaryPositivity.TriangularDynamics.admissible_polynomial_expansion` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Witness/ElementarySingletonCoefficient.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.historyWeight_positive)

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom059

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

lemma historyWeight_positive (l:HistoryLeaf G) : LaurentPositive.Positive (historyWeight G l):= by
  sorry

end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
