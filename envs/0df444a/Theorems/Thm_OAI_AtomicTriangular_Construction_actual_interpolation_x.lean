-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actual_interpolation_x
-- name    : OAI.AtomicTriangular.Construction.actual_interpolation_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:53:30.224205+00:00
-- url     : https://prove2.me/theorems/5d42e698-18c7-452c-8e86-51028a8b2b05
-- title:
--   OAI.AtomicTriangular.Construction.actual_interpolation_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actual_interpolation` of [lean/OAI/Analysis/Triangular/Construction/ActualInterpolation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualInterpolation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open Complex Matrix`):
--
--   ```lean
--   lemma actual_interpolation_x {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
--       actualJ 0 z hz hzB n.val=gaussianG z n.val ∧ deriv (actualJ 0 z hz hzB) n.val=deriv (gaussianG z) n.val ∧
--       actualJ 1 z hz hzB n.val=0 ∧ deriv (actualJ 1 z hz hzB) n.val=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.actualJ` and `OAI.AtomicTriangular.Construction.gaussianG` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.Construction.Node`, `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.residues` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualSchwartz_node_x`, `OAI.AtomicTriangular.Construction.actualSchwartz_signs_x` and `OAI.AtomicTriangular.Construction.near_signs_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/ActualInterpolation.lean (declaration OAI.AtomicTriangular.Construction.actual_interpolation)

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
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma actual_interpolation_x {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    actualJ 0 z hz hzB n.val=gaussianG z n.val ∧ deriv (actualJ 0 z hz hzB) n.val=deriv (gaussianG z) n.val ∧
    actualJ 1 z hz hzB n.val=0 ∧ deriv (actualJ 1 z hz hzB) n.val=0 := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
