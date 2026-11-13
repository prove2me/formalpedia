-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_actualJ0_curvature_eu
-- name    : OAI.AtomicTriangular.Construction.actualJ0_curvature_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:03:55.551199+00:00
-- url     : https://prove2.me/theorems/84e3e269-9119-420b-9597-323110b6e241
-- title:
--   OAI.AtomicTriangular.Construction.actualJ0_curvature_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.actualJ0_curvature` of [lean/OAI/Analysis/Triangular/Construction/FarCurvature.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FarCurvature.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open Complex Set`, `open AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma actualJ0_curvature_eu (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
--       (i : Fin 5) (hs : curvaturePoint i ≤ s) (hs14 : 29/2 ≤ s) :
--       |iteratedDeriv 2 (actualJ0 side z hz hzB) s|/2 ≤
--         (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.Z` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.Construction.actualJ0`, `OAI.AtomicTriangular.Construction.curvaturePoint`, `OAI.AtomicTriangular.Construction.finiteCurvatureEnvelope` and `OAI.AtomicTriangular.Construction.tailCurvatureEnvelope` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proof of `OAI.AtomicTriangular.Construction.global_signs_eu` of this split imports it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/FarCurvature.lean (declaration OAI.AtomicTriangular.Construction.actualJ0_curvature)

import Mathlib
import Definitions.Def_OAIQ334E011

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate

lemma actualJ0_curvature_eu (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (i : Fin 5) (hs : curvaturePoint i ≤ s) (hs14 : 29/2 ≤ s) :
    |iteratedDeriv 2 (actualJ0 side z hz hzB) s|/2 ≤
      (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000) := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
