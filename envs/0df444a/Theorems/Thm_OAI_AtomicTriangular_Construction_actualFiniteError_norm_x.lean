-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualFiniteError_norm_x
-- name    : OAI.AtomicTriangular.Construction.actualFiniteError_norm_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:51:15.317938+00:00
-- url     : https://prove2.me/theorems/c1a9db0e-6518-4dc8-bb02-2f86a85681a6
-- title:
--   OAI.AtomicTriangular.Construction.actualFiniteError_norm_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualFiniteError_norm` of [lean/OAI/Analysis/Triangular/Construction/ActualCorrection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualCorrection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma actualFiniteError_norm_x (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
--       ‖actualFiniteError side z hz hzB‖ < (1/10^5:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.FiniteCoefficients` and `OAI.AtomicTriangular.Construction.actualFiniteError` (definitions bundle `OAIQ257X006` of this split); `OAI.AtomicTriangular.Construction.Z` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualTrigonometric_norm_x`, `OAI.AtomicTriangular.Construction.near_signs_x` and `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualCorrection.lean (declaration OAI.AtomicTriangular.Construction.actualFiniteError_norm)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate

lemma actualFiniteError_norm_x (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    ‖actualFiniteError side z hz hzB‖ < (1/10^5:ℝ) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
