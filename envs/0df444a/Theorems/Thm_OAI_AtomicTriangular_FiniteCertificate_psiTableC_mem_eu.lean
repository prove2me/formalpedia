-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_psiTableC_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.psiTableC_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:46:13.358422+00:00
-- url     : https://prove2.me/theorems/3f8d9358-8a3a-422c-af05-d715a0994ec0
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.psiTableC_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.psiTableC_mem` of [lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma psiTableC_mem_eu (i : Fin 15) (j : Fin 31) : (psiTableC i j).Mem (normJetEnvelope (damping 1) (damping 0) (tailBase i) (frequency j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.frequency`, `OAI.AtomicTriangular.Construction.normJetEnvelope` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.tailBase` (definitions bundle `OAIQ334E003` of this split); `OAI.AtomicTriangular.FiniteCertificate.psiTableC` (definitions bundle `OAIQ334E005` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.tail_finite_column_bound_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean (declaration OAI.AtomicTriangular.FiniteCertificate.psiTableC_mem)

import Mathlib
import Definitions.Def_OAIQ334E005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval
lemma psiTableC_mem_eu (i : Fin 15) (j : Fin 31) : (psiTableC i j).Mem (normJetEnvelope (damping 1) (damping 0) (tailBase i) (frequency j)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
