-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_global_signs_tg
-- name    : OAI.AtomicTriangular.Construction.global_signs_tg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T07:34:59.29087+00:00
-- url     : https://prove2.me/theorems/3c6d6b8d-4140-4b21-97d6-3cd30368f215
-- title:
--   OAI.AtomicTriangular.Construction.global_signs_tg: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.global_signs` of [lean/OAI/Analysis/Triangular/Signs/FarSigns.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/FarSigns.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   It is published as a statement of its own so that the definitions bundle holding `largeGaussianPair` can import it, instead of a chain of bundles holding the whole finite sign certificate.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   theorem global_signs_tg {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 0 ≤ s) :
--       actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Z`, `OAI.AtomicTriangular.Construction.actualJ` and `OAI.AtomicTriangular.Construction.gaussianG`, from the definitions bundle `OAIQ262T253` of this split and the bundles it imports.
--
--   **Used by.** The definitions bundle `OAIQ262T261` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Signs/FarSigns.lean (declaration OAI.AtomicTriangular.Construction.global_signs)

import Mathlib
import Definitions.Def_OAIQ262T253

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
theorem global_signs_tg {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 0 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
