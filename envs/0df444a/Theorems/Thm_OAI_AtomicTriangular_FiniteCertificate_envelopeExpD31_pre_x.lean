-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_envelopeExpD31_pre_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.envelopeExpD31_pre_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:36:51.722977+00:00
-- url     : https://prove2.me/theorems/839d6723-c9c5-48dc-9a5f-fbb633a48c2f
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.envelopeExpD31_pre_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.envelopeExpD31_pre` of [lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma envelopeExpD31_pre_x (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 31))).normSq.hi ≤ scale*1024^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.scale`, `OAI.AtomicTriangular.Interval.CI.normSq`, `OAI.AtomicTriangular.Interval.CI.ofReal`, `OAI.AtomicTriangular.Interval.CI`, `OAI.AtomicTriangular.Interval.RI`, `OAI.AtomicTriangular.Interval.RI.mul`, `OAI.AtomicTriangular.Interval.RI.neg` and `OAI.AtomicTriangular.Interval.RI.point` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.envelopePhase00` (definitions bundle `OAIQ257X004` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.psiD31_mem_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopePsiD.lean (declaration OAI.AtomicTriangular.FiniteCertificate.envelopeExpD31_pre)

import Mathlib
import Definitions.Def_OAIQ257X004

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
lemma envelopeExpD31_pre_x (j : Fin 31) : (CI.ofReal (((envelopePhase00 j).re.neg).neg.mul (RI.point 31))).normSq.hi ≤ scale*1024^2 := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
