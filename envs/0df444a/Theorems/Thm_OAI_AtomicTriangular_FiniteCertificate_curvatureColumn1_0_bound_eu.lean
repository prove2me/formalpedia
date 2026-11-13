-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_FiniteCertificate_curvatureColumn1_0_bound_eu
-- name    : OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T20:33:37.095228+00:00
-- url     : https://prove2.me/theorems/d09e4027-7956-4725-acef-d783a7abef38
-- title:
--   OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound` of [lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.FiniteCertificate`, with `open scoped BigOperators`, `open Construction AtomicTriangular.Interval Complex`):
--
--   ```lean
--   lemma curvatureColumn1_0_bound_eu (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 0) c < (291294/100:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.curvaturePoint` and `OAI.AtomicTriangular.Construction.rawCurvatureColumn` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.finiteCurvatureCap_bound_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureSums.lean (declaration OAI.AtomicTriangular.FiniteCertificate.curvatureColumn1_0_bound)

import Mathlib
import Definitions.Def_OAIQ334E011

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
lemma curvatureColumn1_0_bound_eu (c : Fin 22) : rawCurvatureColumn 1 (curvaturePoint 0) c < (291294/100:ℝ) := by
  sorry
end AtomicTriangular.FiniteCertificate
end

end OAI
end
