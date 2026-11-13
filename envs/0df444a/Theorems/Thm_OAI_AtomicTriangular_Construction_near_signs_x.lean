-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_near_signs_x
-- name    : OAI.AtomicTriangular.Construction.near_signs_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:53:28.309202+00:00
-- url     : https://prove2.me/theorems/d5d11fc3-794d-4abc-9823-7bd0308a129f
-- title:
--   OAI.AtomicTriangular.Construction.near_signs_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.near_signs` of [lean/OAI/Analysis/Triangular/Signs/NearSigns.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/NearSigns.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators`, `open Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma near_signs_x {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc 0 (29/2)) :
--       actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.actualJ` and `OAI.AtomicTriangular.Construction.gaussianG` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.Construction.Z` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.actualSchwartz_signs_x` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/NearSigns.lean (declaration OAI.AtomicTriangular.Construction.near_signs)

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
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_signs_x {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc 0 (29/2)) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
