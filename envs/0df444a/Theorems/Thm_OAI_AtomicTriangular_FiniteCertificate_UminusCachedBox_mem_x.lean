-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_UminusCachedBox_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:18:22.961047+00:00
-- url     : https://prove2.me/theorems/b8e49ce8-8d0f-4d6f-8490-f16546ff6b6f
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox_mem` of [lean/OAI/Analysis/Triangular/Certificate/ParamU.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Matrix`):
--
--   ```lean
--   lemma UminusCachedBox_mem_x (i : Fin 20) (j : Fin 8) : (UminusCachedBox i j).Mem (Uminus i j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.Construction.Uminus` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.FiniteCertificate.UminusTable_mem_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/ParamU.lean (declaration OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Matrix
lemma UminusCachedBox_mem_x (i : Fin 20) (j : Fin 8) : (UminusCachedBox i j).Mem (Uminus i j) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
