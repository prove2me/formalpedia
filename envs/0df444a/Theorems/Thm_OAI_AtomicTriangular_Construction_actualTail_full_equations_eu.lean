-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualTail_full_equations_eu
-- name    : OAI.AtomicTriangular.Construction.actualTail_full_equations_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:54:34.2882+00:00
-- url     : https://prove2.me/theorems/92f30b97-e132-4f5f-9fff-6ebbe051ec32
-- title:
--   OAI.AtomicTriangular.Construction.actualTail_full_equations_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualTail_full_equations` of [lean/OAI/Analysis/Triangular/Construction/ActualTail.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualTail.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open AtomicTriangular.L1Kernel AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma actualTail_full_equations_eu {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
--       actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+
--         CallOperator (actualTrigonometric 1 z hz hzB)-AallOperator (actualTrigonometric 0 z hz hzB)+
--         tailTarget z hz hzB+(3/500:ℝ) • tailFixedColumn 22 ∧
--       actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+
--         CallOperator (actualTrigonometric 0 z hz hzB)-AallOperator (actualTrigonometric 1 z hz hzB)-
--         (3/500:ℝ) • tailFixedColumn 22
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.TailNode` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.AallOperator`, `OAI.AtomicTriangular.Construction.CallOperator`, `OAI.AtomicTriangular.Construction.Doperator`, `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.TrigonometricCoefficients`, `OAI.AtomicTriangular.Construction.Z`, `OAI.AtomicTriangular.Construction.actualTail`, `OAI.AtomicTriangular.Construction.actualTrigonometric`, `OAI.AtomicTriangular.Construction.tailFixedColumn` and `OAI.AtomicTriangular.Construction.tailTarget` (definitions bundle `OAIQ334E006` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.actual_interpolation_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualTail.lean (declaration OAI.AtomicTriangular.Construction.actualTail_full_equations)

import Mathlib
import Definitions.Def_OAIQ334E006

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
lemma actualTail_full_equations_eu {z : ℝ} (hz : 0<z) (hzB : z≤Z) :
    actualTail 0 z hz hzB = Doperator (actualTail 1 z hz hzB)+
      CallOperator (actualTrigonometric 1 z hz hzB)-AallOperator (actualTrigonometric 0 z hz hzB)+
      tailTarget z hz hzB+(3/500:ℝ) • tailFixedColumn 22 ∧
    actualTail 1 z hz hzB = Doperator (actualTail 0 z hz hzB)+
      CallOperator (actualTrigonometric 0 z hz hzB)-AallOperator (actualTrigonometric 1 z hz hzB)-
      (3/500:ℝ) • tailFixedColumn 22 := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
