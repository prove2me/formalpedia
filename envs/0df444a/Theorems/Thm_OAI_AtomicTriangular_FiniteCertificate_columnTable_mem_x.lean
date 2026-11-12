-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_columnTable_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.columnTable_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:33:23.536589+00:00
-- url     : https://prove2.me/theorems/fecb62f1-82c5-437f-b116-90b6f54e0657
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.columnTable_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.columnTable_mem` of [lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma columnTable_mem_x (col : Fin 23) (j : Fin 31) : (columnTable col j).Mem (finiteColumn col j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.FiniteCertificate.columnTable` and `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.finiteColumn` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.finiteCurvatureCap_bound_x`, `OAI.AtomicTriangular.Construction.tailFixedColumn_norm_constant_x`, `OAI.AtomicTriangular.Construction.tail_finite_column_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn0_2_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_2_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow13_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow14_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow15_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow17_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow7_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow8_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow9_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullWTable_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.minusResidualBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns0_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns1_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns2_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns4_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns4_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable0_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable2_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable3_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable4_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable5_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderTable6_x`, `OAI.AtomicTriangular.FiniteCertificate.remainder_table_x` and `OAI.AtomicTriangular.FiniteCertificate.spectrumBox_mem_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean (declaration OAI.AtomicTriangular.FiniteCertificate.columnTable_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X000

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
lemma columnTable_mem_x (col : Fin 23) (j : Fin 31) : (columnTable col j).Mem (finiteColumn col j) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
