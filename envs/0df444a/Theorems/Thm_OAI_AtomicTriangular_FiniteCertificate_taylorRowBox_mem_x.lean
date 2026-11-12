-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_taylorRowBox_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_x
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T04:45:43.322558+00:00
-- url     : https://prove2.me/theorems/71bb8f9c-28c3-4457-84ec-1325e6c5f1e9
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem` of [lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma taylorRowBox_mem_x (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) :
--       (taylorRowBox side n y l r).Mem
--         (taylorRow side (nearNode n) (nearDisplacement n y) l.val r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.nearDisplacement`, `OAI.AtomicTriangular.Construction.taylorRow` and `OAI.AtomicTriangular.FiniteCertificate.nearNode` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.FiniteCertificate.taylorRowBox` (definitions bundle `OAIQ257X023` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_2_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_2_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_3_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_4_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_5_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr0_6_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_0_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_0_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_1_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_2_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_3_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_3_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_4_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_0_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_5_1_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.tr1_6_0_mem_x` and `OAI.AtomicTriangular.FiniteCertificate.tr1_6_1_mem_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Taylor/TaylorRowsBase.lean (declaration OAI.AtomicTriangular.FiniteCertificate.taylorRowBox_mem)

import Mathlib
import Definitions.Def_OAIQ257X023

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

lemma taylorRowBox_mem_x (side : Fin 2) (n : Fin 7) (y : Fin 2) (l : Fin 21) (r : Fin 8) :
    (taylorRowBox side n y l r).Mem
      (taylorRow side (nearNode n) (nearDisplacement n y) l.val r) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
