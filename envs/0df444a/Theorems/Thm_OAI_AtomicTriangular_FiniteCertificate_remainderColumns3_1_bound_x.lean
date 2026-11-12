-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderColumns3_1_bound_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:23:10.514201+00:00
-- url     : https://prove2.me/theorems/ae3e18bf-51cf-4e14-8c3a-56b8c7608a51
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound` of [lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainderColumns3_1_bound_x (c : Fin 22) : rawRemainderColumn 1 3 c < (1033019/1000000000000000:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.rawRemainderColumn` (definitions bundle `OAIQ257X011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.remainderTable3_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderSums3.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainderColumns3_1_bound)

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
lemma remainderColumns3_1_bound_x (c : Fin 22) : rawRemainderColumn 1 3 c < (1033019/1000000000000000:ℝ) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
