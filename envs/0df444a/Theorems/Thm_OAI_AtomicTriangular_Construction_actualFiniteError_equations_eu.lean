-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualFiniteError_equations_eu
-- name    : OAI.AtomicTriangular.Construction.actualFiniteError_equations_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:57:43.85093+00:00
-- url     : https://prove2.me/theorems/f1366331-3277-4120-9993-c0552aafb9bb
-- title:
--   OAI.AtomicTriangular.Construction.actualFiniteError_equations_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualFiniteError_equations` of [lean/OAI/Analysis/Triangular/Construction/ActualInput.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualInput.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds`):
--
--   ```lean
--   lemma actualFiniteError_equations_eu {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
--       actualFiniteError 0 z hz hzB = Roperator (actualFiniteError 1 z hz hzB)+Boperator (actualTail 1 z hz hzB)+finiteResidual z ∧
--       actualFiniteError 1 z hz hzB = Roperator (actualFiniteError 0 z hz hzB)+Boperator (actualTail 0 z hz hzB)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.TailNode` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.Boperator`, `OAI.AtomicTriangular.Construction.FiniteCoefficients`, `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.Z`, `OAI.AtomicTriangular.Construction.actualFiniteError`, `OAI.AtomicTriangular.Construction.actualTail` and `OAI.AtomicTriangular.Construction.finiteResidual` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.Construction.Roperator` (definitions bundle `OAIQ334E009` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.actual_interpolation_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualInput.lean (declaration OAI.AtomicTriangular.Construction.actualFiniteError_equations)

import Mathlib
import Definitions.Def_OAIQ334E009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open AtomicTriangular.L1Kernel AtomicTriangular.MatrixBounds

lemma actualFiniteError_equations_eu {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualFiniteError 0 z hz hzB = Roperator (actualFiniteError 1 z hz hzB)+Boperator (actualTail 1 z hz hzB)+finiteResidual z ∧
    actualFiniteError 1 z hz hzB = Roperator (actualFiniteError 0 z hz hzB)+Boperator (actualTail 0 z hz hzB) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
