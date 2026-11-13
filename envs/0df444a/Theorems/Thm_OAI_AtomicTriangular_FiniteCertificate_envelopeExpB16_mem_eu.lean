-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_envelopeExpB16_mem_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_mem_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T11:39:08.268997+00:00
-- url     : https://prove2.me/theorems/c00769b5-7e13-45f8-a03d-22070f75f2c3
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_mem_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_mem` of [lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma envelopeExpB16_mem_eu (j : Fin 31) : (envelopeExpB16 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*16))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.frequency`, `OAI.AtomicTriangular.Construction.frequencyDecay`, `OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ334E000` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.psiTableB_mem_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiB.lean (declaration OAI.AtomicTriangular.FiniteCertificate.envelopeExpB16_mem)

import Mathlib
import Definitions.Def_OAIQ334E000

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
lemma envelopeExpB16_mem_eu (j : Fin 31) : (envelopeExpB16 j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 1) (frequency j)*16)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
