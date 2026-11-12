-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderTable3_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainderTable3_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:23:58.020211+00:00
-- url     : https://prove2.me/theorems/81e65e00-c562-4920-b4f9-07091b3c623a
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainderTable3_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainderTable3` of [lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainderTable3_x (c d : Fin 22) : 3*(rawRemainderColumn 0 3 c+rawRemainderColumn 1 3 d)+(6/1000)*(rawRemainderConstant 0 3+rawRemainderConstant 1 3) < (75/10000000:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.rawRemainderColumn` and `OAI.AtomicTriangular.Construction.rawRemainderConstant` (definitions bundle `OAIQ257X011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.remainder_table_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainderTable3)

import Mathlib
import Definitions.Def_OAIQ257X011

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
lemma remainderTable3_x (c d : Fin 22) : 3*(rawRemainderColumn 0 3 c+rawRemainderColumn 1 3 d)+(6/1000)*(rawRemainderConstant 0 3+rawRemainderConstant 1 3) < (75/10000000:ℝ) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
