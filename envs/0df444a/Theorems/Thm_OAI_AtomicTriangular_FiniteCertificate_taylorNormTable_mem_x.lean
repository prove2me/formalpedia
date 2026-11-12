-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorNormTable_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.taylorNormTable_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:33:55.216282+00:00
-- url     : https://prove2.me/theorems/87ba64d5-ded3-4d11-a202-b9d16b6d2512
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.taylorNormTable_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.taylorNormTable_mem` of [lean/OAI/Analysis/Triangular/Signs/RemainderNorm.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderNorm.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma taylorNormTable_mem_x (q br : Fin 2) (j : Fin 31) : (taylorNormTable q br j).Mem ‖taylorPhase q br (frequency j)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.taylorPhase` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.FiniteCertificate.taylorNormTable` (definitions bundle `OAIQ257X019` of this split); `OAI.AtomicTriangular.Construction.frequency` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.remainderColumns5_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderColumns6_1_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderConst0_0_bound_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_01_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData0_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.remainderData1_00_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.remainderData6_01_mem_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/RemainderNorm.lean (declaration OAI.AtomicTriangular.FiniteCertificate.taylorNormTable_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008
import Definitions.Def_OAIQ257X019

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
lemma taylorNormTable_mem_x (q br : Fin 2) (j : Fin 31) : (taylorNormTable q br j).Mem ‖taylorPhase q br (frequency j)‖ := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
