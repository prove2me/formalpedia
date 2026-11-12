-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_signs_x
-- name    : OAI.AtomicTriangular.Construction.actualSchwartz_signs_x
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T03:53:26.743204+00:00
-- url     : https://prove2.me/theorems/8146bc04-e6c3-482c-a245-383b34d1c31e
-- title:
--   OAI.AtomicTriangular.Construction.actualSchwartz_signs_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualSchwartz_signs` of [lean/OAI/Analysis/Triangular/Construction/Normalization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators FourierTransform SchwartzMap`, `open Complex`):
--
--   ```lean
--   lemma actualSchwartz_signs_x {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
--       actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
--         0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.actualSchwartz` (definitions bundle `OAIQ257X006` of this split); `OAI.AtomicTriangular.Construction.gaussianZ_bounds` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.gaussian`, `OAI.AtomicTriangular.Construction.Plane`, `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.gaussianZ` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The definitions bundles `OAIQ257X029` and `OAIQ257X034` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean (declaration OAI.AtomicTriangular.Construction.actualSchwartz_signs)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X008

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
lemma actualSchwartz_signs_x {α : ℝ} (hα : 1 ≤ α) (x : Plane) :
    actualSchwartz 0 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x ≤ AtomicTriangular.gaussian α x ∧
      0 ≤ actualSchwartz 1 (gaussianZ α) (gaussianZ_bounds hα).1 (gaussianZ_bounds hα).2.le x := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
