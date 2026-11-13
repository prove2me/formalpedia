-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainder_table_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainder_table_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:15:54.430407+00:00
-- url     : https://prove2.me/theorems/ac8dd65d-cc54-4052-ba4a-1c8f5c84d5d7
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainder_table_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainder_table` of [lean/OAI/Analysis/Triangular/Signs/RemainderPre.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderPre.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainder_table_eu (n : Fin 7) (c d : Fin 22) :
--       3*(rawRemainderColumn 0 n c+rawRemainderColumn 1 n d)+(6/1000)*(rawRemainderConstant 0 n+rawRemainderConstant 1 n) <
--         (if n.val=0 then (161/100000:ℝ) else 75/10000000)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.rawRemainderColumn` and `OAI.AtomicTriangular.Construction.rawRemainderConstant` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.finiteTaylor_error_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderPre.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainder_table)

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
lemma remainder_table_eu (n : Fin 7) (c d : Fin 22) :
    3*(rawRemainderColumn 0 n c+rawRemainderColumn 1 n d)+(6/1000)*(rawRemainderConstant 0 n+rawRemainderConstant 1 n) <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
