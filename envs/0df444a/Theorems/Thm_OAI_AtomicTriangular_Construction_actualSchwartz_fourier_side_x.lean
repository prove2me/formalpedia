-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_side_x
-- name    : OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T03:51:24.400879+00:00
-- url     : https://prove2.me/theorems/2cf62eee-438a-45e7-a00a-86e8c6073608
-- title:
--   OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side` of [lean/OAI/Analysis/Triangular/Construction/Normalization.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators FourierTransform SchwartzMap`, `open Complex`):
--
--   ```lean
--   lemma actualSchwartz_fourier_side_x (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
--       realFourier (actualSchwartz side z hz hzB) x=(actualSchwartz (otherSide side) z hz hzB x:ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.actualSchwartz` and `OAI.AtomicTriangular.Construction.otherSide` (definitions bundle `OAIQ257X006` of this split); `OAI.AtomicTriangular.realFourier`, `OAI.AtomicTriangular.Construction.Plane` and `OAI.AtomicTriangular.Construction.Z` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x` and the definitions bundles `OAIQ257X029` and `OAIQ257X034` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/Normalization.lean (declaration OAI.AtomicTriangular.Construction.actualSchwartz_fourier_side)

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
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_fourier_side_x (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz side z hz hzB) x=(actualSchwartz (otherSide side) z hz hzB x:ℂ) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
