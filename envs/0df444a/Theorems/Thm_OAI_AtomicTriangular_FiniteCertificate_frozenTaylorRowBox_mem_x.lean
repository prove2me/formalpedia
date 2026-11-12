-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_frozenTaylorRowBox_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T04:35:25.143223+00:00
-- url     : https://prove2.me/theorems/99a98bf0-4c7b-4a77-943f-3eae63755f9a
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem` of [lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval`):
--
--   ```lean
--   lemma frozenTaylorRowBox_mem_x {z : RI} {x : ℝ} (hz : z.Mem x) (l : Fin 21) (r : Fin 8) :
--       (frozenTaylorRowBox z l r).Mem (frozenTaylorRow x l.val r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI` and `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.Construction.frozenTaylorRow` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox` (definitions bundle `OAIQ257X020` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.exceptional_rational_comparison_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/ExceptionalInterval.lean (declaration OAI.AtomicTriangular.FiniteCertificate.frozenTaylorRowBox_mem)

import Mathlib
import Definitions.Def_OAIQ257X011
import Definitions.Def_OAIQ257X020

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

lemma frozenTaylorRowBox_mem_x {z : RI} {x : ℝ} (hz : z.Mem x) (l : Fin 21) (r : Fin 8) :
    (frozenTaylorRowBox z l r).Mem (frozenTaylorRow x l.val r) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
