-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_remainderData6_01_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:27:45.818607+00:00
-- url     : https://prove2.me/theorems/8cbf165a-35b5-47a9-af50-f781afb82267
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem` of [lean/OAI/Analysis/Triangular/Signs/RemainderData6.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData6.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma remainderData6_01_mem_eu (j : Fin 31) : (remainderData6_01 j).Mem (remainderWave 0 1 (nearNode 6) (nearRadius 6) (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.frequency` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.nearRadius`, `OAI.AtomicTriangular.Construction.remainderWave` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ334E011` of this split); `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01` (definitions bundle `OAIQ334E020` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.remainderTable6_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderData6.lean (declaration OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem)

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E020

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
lemma remainderData6_01_mem_eu (j : Fin 31) : (remainderData6_01 j).Mem (remainderWave 0 1 (nearNode 6) (nearRadius 6) (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
