-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_signs_eu
-- name    : OAI.AtomicTriangular.Construction.actualSchwartz_signs_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:57:13.880831+00:00
-- url     : https://prove2.me/theorems/011658ae-e145-4868-803e-71b40c4c7377
-- title:
--   OAI.AtomicTriangular.Construction.actualSchwartz_signs_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualSchwartz_signs` of [lean/OAI/Analysis/Triangular/Construction/Normalization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators FourierTransform SchwartzMap`, `open Complex`):
--
--   ```lean
--   lemma actualSchwartz_signs_eu {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
--       actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
--         0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Plane`, `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.actualSchwartz` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.gaussian` (definitions bundle `OAIQ334E008` of this split); `OAI.AtomicTriangular.Construction.gaussianZ` and `OAI.AtomicTriangular.Construction.gaussianZ_bounds` (definitions bundle `OAIQ334E009` of this split).
--
--   **Used by.** The definitions bundle `OAIQ334E033` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean (declaration OAI.AtomicTriangular.Construction.actualSchwartz_signs)

import Mathlib
import Definitions.Def_OAIQ334E009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_signs_eu {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
      0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
