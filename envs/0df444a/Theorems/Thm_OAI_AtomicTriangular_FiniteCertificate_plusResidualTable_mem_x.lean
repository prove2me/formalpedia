-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_plusResidualTable_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.plusResidualTable_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:03:27.248936+00:00
-- url     : https://prove2.me/theorems/73d95c2c-064c-41e5-bace-32bdbbf00d7c
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.plusResidualTable_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.plusResidualTable_mem` of [lean/OAI/Analysis/Triangular/Certificate/Inverse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix`):
--
--   ```lean
--   lemma plusResidualTable_mem_x (i j : Fin 20) :
--       (plusResidualTable i j).Mem ((plusApprox*(1 + Construction.R)-1) i j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.plusApprox` (definitions bundle `OAIQ257X009` of this split); `OAI.AtomicTriangular.FiniteCertificate.plusResidualTable` (definitions bundle `OAIQ257X010` of this split); `OAI.AtomicTriangular.Construction.R` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.correctionFinite_small_x`, `OAI.AtomicTriangular.Construction.correctionTail_small_x`, `OAI.AtomicTriangular.FiniteCertificate.UminusCachedBox_mem_x` and `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean (declaration OAI.AtomicTriangular.FiniteCertificate.plusResidualTable_mem)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix
lemma plusResidualTable_mem_x (i j : Fin 20) :
    (plusResidualTable i j).Mem ((plusApprox*(1 + Construction.R)-1) i j) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
