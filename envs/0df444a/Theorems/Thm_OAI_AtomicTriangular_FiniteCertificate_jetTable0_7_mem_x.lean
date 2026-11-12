-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_jetTable0_7_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.jetTable0_7_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:57:38.508412+00:00
-- url     : https://prove2.me/theorems/ae2c6ecf-6023-42c8-8cda-d604d1068d6f
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.jetTable0_7_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.jetTable0_7_mem` of [lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma jetTable0_7_mem_x (j : Fin 31) : (jetTable0_7 j).Mem
--       (jetMultiplier (damping 0) H (finiteNode ⟨3,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping` and `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.jetTable0_7` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.Construction.H`, `OAI.AtomicTriangular.Construction.finiteNode`, `OAI.AtomicTriangular.Construction.frequency` and `OAI.AtomicTriangular.Construction.jetMultiplier` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.jetTable_mem_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean (declaration OAI.AtomicTriangular.FiniteCertificate.jetTable0_7_mem)

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
lemma jetTable0_7_mem_x (j : Fin 31) : (jetTable0_7 j).Mem
    (jetMultiplier (damping 0) H (finiteNode ⟨3,by norm_num⟩) ⟨1,by norm_num⟩ (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
