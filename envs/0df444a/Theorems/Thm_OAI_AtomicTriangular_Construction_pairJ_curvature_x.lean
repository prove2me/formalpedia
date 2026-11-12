-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_pairJ_curvature_x
-- name    : OAI.AtomicTriangular.Construction.pairJ_curvature_x
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:58.234006+00:00
-- url     : https://prove2.me/theorems/f5a2c9ef-454f-488f-a676-f1d33e0fc8d0
-- title:
--   OAI.AtomicTriangular.Construction.pairJ_curvature_x: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.sharp_gaussian_minorants_atomic`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.pairJ_curvature` of [lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open Complex AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma pairJ_curvature_x (a b : TrigonometricCoefficients) (w v : TailCoefficients)
--       (i : Fin 5) {s aL aT : ℝ} (hs : curvaturePoint i≤ s)
--       (ha : ‖a‖≤aL) (hb : ‖b‖≤aL) (hw : ‖w‖≤aT) (hv : ‖v‖≤aT) :
--       |iteratedDeriv 2 (pairJ (coefficientInput 0 a w) (coefficientInput 0 b v)) s|/2≤
--         aL*finiteCurvatureEnvelope i+aT*tailCurvatureEnvelope i
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.TrigonometricCoefficients` and `OAI.AtomicTriangular.Construction.coefficientInput` (definitions bundle `OAIQ257X006` of this split); `OAI.AtomicTriangular.Construction.pairJ` (definitions bundle `OAIQ257X008` of this split); `OAI.AtomicTriangular.Construction.curvaturePoint`, `OAI.AtomicTriangular.Construction.finiteCurvatureEnvelope` and `OAI.AtomicTriangular.Construction.tailCurvatureEnvelope` (definitions bundle `OAIQ257X011` of this split); `OAI.AtomicTriangular.Construction.TailNode` (the published bundle `Def_AtomicGaussian`).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualJ0_deleted_x` and `OAI.AtomicTriangular.Construction.near_signs_x` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean (declaration OAI.AtomicTriangular.Construction.pairJ_curvature)

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
open scoped BigOperators lp
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma pairJ_curvature_x (a b : TrigonometricCoefficients) (w v : TailCoefficients)
    (i : Fin 5) {s aL aT : ℝ} (hs : curvaturePoint i≤ s)
    (ha : ‖a‖≤aL) (hb : ‖b‖≤aL) (hw : ‖w‖≤aT) (hv : ‖v‖≤aT) :
    |iteratedDeriv 2 (pairJ (coefficientInput 0 a w) (coefficientInput 0 b v)) s|/2≤
      aL*finiteCurvatureEnvelope i+aT*tailCurvatureEnvelope i := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
