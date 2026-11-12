-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData1_01_calc_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainderData1_01_calc_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:40:25.31028+00:00
-- url     : https://prove2.me/theorems/c6e42cfd-403e-4199-b02e-e7d22328b252
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainderData1_01_calc_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainderData1_01_calc` of [lean/OAI/Analysis/Triangular/Signs/RemainderData1.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData1.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainderData1_01_calc_x (j : Fin 31) : remainderBox 0 1 1 j (taylorNormTable 0 1 j)=remainderData1_01 j
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.taylorNormTable` (definitions bundle `OAIQ257X019` of this split); `OAI.AtomicTriangular.FiniteCertificate.remainderData1_01` (definitions bundle `OAIQ257X020` of this split); `OAI.AtomicTriangular.FiniteCertificate.remainderBox` (definitions bundle `OAIQ257X021` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.remainder_table_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData1.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainderData1_01_calc)

import Mathlib
import Definitions.Def_OAIQ257X021

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
lemma remainderData1_01_calc_x (j : Fin 31) : remainderBox 0 1 1 j (taylorNormTable 0 1 j)=remainderData1_01 j := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
