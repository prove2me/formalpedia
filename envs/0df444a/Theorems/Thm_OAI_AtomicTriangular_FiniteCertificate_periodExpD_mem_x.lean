-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_periodExpD_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.periodExpD_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:38:19.646197+00:00
-- url     : https://prove2.me/theorems/337aba22-4c1c-429f-99de-5a54b7e8dd12
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.periodExpD_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.periodExpD_mem` of [lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma periodExpD_mem_x (j : Fin 31) : (periodExpD j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*36))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.damping`, `OAI.AtomicTriangular.Construction.frequencyDecay` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.periodExpD` (definitions bundle `OAIQ257X004` of this split); `OAI.AtomicTriangular.Construction.frequency` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.tailFixedColumn_norm_constant_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Envelope/EnvelopeSums.lean (declaration OAI.AtomicTriangular.FiniteCertificate.periodExpD_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
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
open Construction AtomicTriangular.Interval
lemma periodExpD_mem_x (j : Fin 31) : (periodExpD j).Mem (Real.exp (-frequencyDecay (damping 0) (damping 0) (frequency j)*36)) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
