-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorWaveBox_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:30:30.564167+00:00
-- url     : https://prove2.me/theorems/eeb56df0-9095-40a1-a851-cf9f2137d64f
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem` of [lean/OAI/Analysis/Triangular/Taylor/TaylorWave.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma taylorWaveBox_mem_eu (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
--       (taylorWaveBox q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.frequency` and `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.taylorWave` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ334E011` of this split); `OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox` (definitions bundle `OAIQ334E025` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_0_6_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_3_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_6_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw0_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_3_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_1_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.tw1_1_6_mem_eu` and `OAI.AtomicTriangular.FiniteCertificate.tw1_1_mem_eu` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorWave.lean (declaration OAI.AtomicTriangular.FiniteCertificate.taylorWaveBox_mem)

import Mathlib
import Definitions.Def_OAIQ334E011
import Definitions.Def_OAIQ334E025

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
lemma taylorWaveBox_mem_eu (q br : Fin 2) (n : Fin 7) (l : Fin 21) (j : Fin 31) :
    (taylorWaveBox q br n l j).Mem (taylorWave q br (nearNode n) l.val (frequency j)) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
