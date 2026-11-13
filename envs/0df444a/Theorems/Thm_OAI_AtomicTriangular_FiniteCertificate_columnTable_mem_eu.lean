-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.columnTable_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:38:49.438202+00:00
-- url     : https://prove2.me/theorems/9a80141c-1a18-47b4-b384-573c3cf6fb85
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.columnTable_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.columnTable_mem` of [lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma columnTable_mem_eu (col : Fin 23) (j : Fin 31) : (columnTable col j).Mem (finiteColumn col j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.finiteColumn`, `OAI.AtomicTriangular.FiniteCertificate.columnTable` and `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ334E000` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.tailFixedColumn_norm_constant_eu`, `OAI.AtomicTriangular.Construction.tail_finite_column_bound_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem_eu` and `OAI.AtomicTriangular.FiniteCertificate.fullWTable_mem_eu` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean (declaration OAI.AtomicTriangular.FiniteCertificate.columnTable_mem)

import Mathlib
import Definitions.Def_OAIQ334E000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma columnTable_mem_eu (col : Fin 23) (j : Fin 31) : (columnTable col j).Mem (finiteColumn col j) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
