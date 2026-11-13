-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_fullJetRow19_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:57:55.873217+00:00
-- url     : https://prove2.me/theorems/4608b06d-cf89-43b6-a0b8-d5dbb7de66c1
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem` of [lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma fullJetRow19_mem_eu (col : Fin 23) : (fullJetRow19 col).Mem (fullJetMatrix 19 col)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.fullJetMatrix` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.FiniteCertificate.fullJetRow19` (definitions bundle `OAIQ334E009` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.plusBlockBox_mem_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/JetMatrix.lean (declaration OAI.AtomicTriangular.FiniteCertificate.fullJetRow19_mem)

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
lemma fullJetRow19_mem_eu (col : Fin 23) : (fullJetRow19 col).Mem (fullJetMatrix 19 col) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
