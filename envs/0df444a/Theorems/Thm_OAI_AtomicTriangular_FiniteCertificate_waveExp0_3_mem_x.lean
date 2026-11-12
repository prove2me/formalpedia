-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_waveExp0_3_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.waveExp0_3_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:00:01.20761+00:00
-- url     : https://prove2.me/theorems/45cf9245-01d1-4ec8-85f7-23273fef4b48
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.waveExp0_3_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.waveExp0_3_mem` of [lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma waveExp0_3_mem_x (j : Fin 31) : (waveExp0_3 j).Mem
--       (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((3:ℤ):ℂ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping` and `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.waveExp0_3` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.Construction.frequency` and `OAI.AtomicTriangular.Construction.zeta` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.jetTable0_17_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_7_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_8_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable0_9_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_12_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_13_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_14_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_15_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_16_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_17_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_7_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_8_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.jetTable1_9_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.jetTable_mem_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveExpData.lean (declaration OAI.AtomicTriangular.FiniteCertificate.waveExp0_3_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008

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
lemma waveExp0_3_mem_x (j : Fin 31) : (waveExp0_3 j).Mem
    (exp (I*Real.pi*zeta (damping 0) (damping 1) (frequency j)*((3:ℤ):ℂ))) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
