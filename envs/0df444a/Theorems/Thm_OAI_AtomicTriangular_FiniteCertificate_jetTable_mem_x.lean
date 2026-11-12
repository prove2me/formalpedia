-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_jetTable_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.jetTable_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:58:11.503234+00:00
-- url     : https://prove2.me/theorems/c7d4608a-e86e-4c05-bca1-c47e95657d6f
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.jetTable_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.jetTable_mem` of [lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma jetTable_mem_x (q : Fin 2) (i : Fin 20) (j : Fin 31) : (jetTable q i j).Mem
--       (jetMultiplier (damping q) H (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping` and `OAI.AtomicTriangular.Interval.CI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.jetTable` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.Construction.H`, `OAI.AtomicTriangular.Construction.finiteNode`, `OAI.AtomicTriangular.Construction.frequency` and `OAI.AtomicTriangular.Construction.jetMultiplier` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow10_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow11_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow13_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow14_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow15_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow17_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow2_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow3_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow4_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow5_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow6_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow7_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow8_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow9_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.minusResidualBox_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.plusResidualBox_mem_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/WaveJetsData.lean (declaration OAI.AtomicTriangular.FiniteCertificate.jetTable_mem)

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
lemma jetTable_mem_x (q : Fin 2) (i : Fin 20) (j : Fin 31) : (jetTable q i j).Mem
    (jetMultiplier (damping q) H (finiteNode ⟨i.val/2,by omega⟩) ⟨i.val%2,by omega⟩ (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
