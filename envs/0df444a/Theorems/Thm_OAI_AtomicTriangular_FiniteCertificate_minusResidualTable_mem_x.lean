-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_minusResidualTable_mem_x
-- name    : OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:02:47.739427+00:00
-- url     : https://prove2.me/theorems/1ff0a802-613a-4914-996c-4639c200a634
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem` of [lean/OAI/Analysis/Triangular/Certificate/Inverse.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval AtomicTriangular.MatrixBounds Matrix`):
--
--   ```lean
--   lemma minusResidualTable_mem_x (i j : Fin 20) :
--       (minusResidualTable i j).Mem ((minusApprox*(1 - Construction.R)-1) i j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Interval.RI.Mem` (definitions bundle `OAIQ257X000` of this split); `OAI.AtomicTriangular.FiniteCertificate.minusApprox` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.FiniteCertificate.minusResidualTable` (definitions bundle `OAIQ257X010` of this split); `OAI.AtomicTriangular.Construction.R` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.FiniteCertificate.UplusCachedBox_mem_x`, `OAI.AtomicTriangular.FiniteCertificate.minusInverse_bound_x` and `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Certificate/Inverse.lean (declaration OAI.AtomicTriangular.FiniteCertificate.minusResidualTable_mem)

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
lemma minusResidualTable_mem_x (i j : Fin 20) :
    (minusResidualTable i j).Mem ((minusApprox*(1 - Construction.R)-1) i j) := by
  sorry

end AtomicTriangular.FiniteCertificate
end

end OAI
end
