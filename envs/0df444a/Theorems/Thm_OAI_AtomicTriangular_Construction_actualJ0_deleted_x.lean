-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualJ0_deleted_x
-- name    : OAI.AtomicTriangular.Construction.actualJ0_deleted_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:03:02.861916+00:00
-- url     : https://prove2.me/theorems/4a1bde98-bbab-44f1-bac0-42f163c740fa
-- title:
--   OAI.AtomicTriangular.Construction.actualJ0_deleted_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualJ0_deleted` of [lean/OAI/Analysis/Triangular/Signs/FarSigns.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/FarSigns.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma actualJ0_deleted_x (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
--       (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
--       (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ)) :
--       |deletedSecond (actualJ0 side z hz hzB) n.val s| ≤ farK i
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.actualJ0`, `OAI.AtomicTriangular.Construction.curvaturePoint`, `OAI.AtomicTriangular.Construction.deletedSecond` and `OAI.AtomicTriangular.Construction.farK` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.Construction.Node`, `OAI.AtomicTriangular.Construction.Z` and `OAI.AtomicTriangular.Construction.residues` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.actualSchwartz_signs_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/FarSigns.lean (declaration OAI.AtomicTriangular.Construction.actualJ0_deleted)

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma actualJ0_deleted_x (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ)) :
    |deletedSecond (actualJ0 side z hz hzB) n.val s| ≤ farK i := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
