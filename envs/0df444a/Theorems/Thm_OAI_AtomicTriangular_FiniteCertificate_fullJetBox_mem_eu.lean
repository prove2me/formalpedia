-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetBox_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:58:02.429355+00:00
-- url     : https://prove2.me/theorems/5b92fcbd-fb8d-4612-bf38-432eaa5a5923
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem` of [lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma fullJetBox_mem_eu (i : Fin 20) (col : Fin 23) : (fullJetBox i col).Mem (fullJetMatrix i col)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.fullJetMatrix` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.FiniteCertificate.fullJetBox` (definitions bundle `OAIQ334E009` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.R0Box_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow0_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow10_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow11_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow12_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow13_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow14_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow15_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow17_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow2_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow4_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow5_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow6_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow7_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow8_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.fullJetRow9_mem_eu`, `OAI.AtomicTriangular.FiniteCertificate.minusBlockBox_mem_eu` and `OAI.AtomicTriangular.FiniteCertificate.plusBlockBox_mem_eu` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean (declaration OAI.AtomicTriangular.FiniteCertificate.fullJetBox_mem)

import Mathlib
import Definitions.Def_OAIQ334E009

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
lemma fullJetBox_mem_eu (i : Fin 20) (col : Fin 23) : (fullJetBox i col).Mem (fullJetMatrix i col) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
