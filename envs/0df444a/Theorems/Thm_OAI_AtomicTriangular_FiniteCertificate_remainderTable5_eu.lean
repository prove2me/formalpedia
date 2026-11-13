-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderTable5_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainderTable5_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:15:26.989735+00:00
-- url     : https://prove2.me/theorems/bd1dfbce-9ed7-4fed-8dbe-4dd3c1ae8a91
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainderTable5_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainderTable5` of [lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainderTable5_eu (c d : Fin 22) : 3*(rawRemainderColumn 0 5 c+rawRemainderColumn 1 5 d)+(6/1000)*(rawRemainderConstant 0 5+rawRemainderConstant 1 5) < (75/10000000:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.rawRemainderColumn` and `OAI.AtomicTriangular.Construction.rawRemainderConstant` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.remainder_table_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums5.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainderTable5)

import Mathlib
import Definitions.Def_OAIQ334E011

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
lemma remainderTable5_eu (c d : Fin 22) : 3*(rawRemainderColumn 0 5 c+rawRemainderColumn 1 5 d)+(6/1000)*(rawRemainderConstant 0 5+rawRemainderConstant 1 5) < (75/10000000:ℝ) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
