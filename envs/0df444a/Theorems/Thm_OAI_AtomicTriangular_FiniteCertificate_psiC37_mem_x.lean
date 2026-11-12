-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_psiC37_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.psiC37_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:39:22.745655+00:00
-- url     : https://prove2.me/theorems/aa244c93-f92e-49e6-97d0-5764fee3838e
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.psiC37_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.psiC37_mem` of [lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma psiC37_mem_x (j : Fin 31) : (psiC37 j).Mem (normJetEnvelope (damping 1) (damping 0) 37 (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.normJetEnvelope` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.psiC37` (definitions bundle `OAIQ257X005` of this split); `OAI.AtomicTriangular.Construction.frequency` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.psiTableC_mem_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiC.lean (declaration OAI.AtomicTriangular.FiniteCertificate.psiC37_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X005

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
lemma psiC37_mem_x (j : Fin 31) : (psiC37 j).Mem (normJetEnvelope (damping 1) (damping 0) 37 (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
