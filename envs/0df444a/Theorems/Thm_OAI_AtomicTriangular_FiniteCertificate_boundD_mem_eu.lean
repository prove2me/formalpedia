-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_boundD_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.boundD_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:41:42.950205+00:00
-- url     : https://prove2.me/theorems/c5f5b7f1-4a63-4817-abd4-be8853130be4
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.boundD_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.boundD_mem` of [lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma boundD_mem_eu (c : Fin 2) : (boundD c).Mem (tailTailEnvelope c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.tailTailEnvelope` and `OAI.AtomicTriangular.FiniteCertificate.boundD` (definitions bundle `OAIQ334E004` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.Dkernel_bound_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean (declaration OAI.AtomicTriangular.FiniteCertificate.boundD_mem)

import Mathlib
import Definitions.Def_OAIQ334E004

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
lemma boundD_mem_eu (c : Fin 2) : (boundD c).Mem (tailTailEnvelope c) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
