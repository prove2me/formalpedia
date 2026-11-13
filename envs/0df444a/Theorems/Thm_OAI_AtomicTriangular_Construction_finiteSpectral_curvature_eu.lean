-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_Construction_finiteSpectral_curvature_eu
-- name    : OAI.AtomicTriangular.Construction.finiteSpectral_curvature_eu
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:24.553225+00:00
-- url     : https://prove2.me/theorems/39c3431d-d557-4c94-bdb8-5cdd8fd91076
-- title:
--   OAI.AtomicTriangular.Construction.finiteSpectral_curvature_eu: intermediate lemma from OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AtomicTriangular.Construction.finiteSpectral_curvature` of [lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AtomicTriangular.Construction`, with `open scoped BigOperators lp`, `open Complex AtomicTriangular.FiniteCertificate`):
--
--   ```lean
--   lemma finiteSpectral_curvature_eu (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
--       (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
--       ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖≤‖a‖*finiteCurvatureCap br i
--   ```
--
--   **Definitions.** The statement is written with `OAI.AtomicTriangular.Construction.TailNode` (definitions bundle `OAIQ334E000` of this split); `OAI.AtomicTriangular.Construction.TailCoefficients`, `OAI.AtomicTriangular.Construction.TrigonometricCoefficients` and `OAI.AtomicTriangular.Construction.coefficientInput` (definitions bundle `OAIQ334E006` of this split); `OAI.AtomicTriangular.Construction.Spectrum` and `OAI.AtomicTriangular.Construction.finiteSpectral` (definitions bundle `OAIQ334E007` of this split); `OAI.AtomicTriangular.Construction.waveFunctionJet` (definitions bundle `OAIQ334E009` of this split); `OAI.AtomicTriangular.Construction.curvaturePoint` and `OAI.AtomicTriangular.Construction.finiteCurvatureCap` (definitions bundle `OAIQ334E011` of this split).
--
--   **Used by.** The proofs of `OAI.AtomicTriangular.Construction.actualJ0_curvature_eu` and `OAI.AtomicTriangular.Construction.deleted_accuracy_eu` of this split import it.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Construction/CurvatureEnvelope.lean (declaration OAI.AtomicTriangular.Construction.finiteSpectral_curvature)

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
namespace AtomicTriangular.Construction
open Complex AtomicTriangular.FiniteCertificate

lemma finiteSpectral_curvature_eu (C : ℝ) (a : TrigonometricCoefficients) (w : TailCoefficients)
    (br : Fin 2) (i : Fin 5) {s : ℝ} (hs : curvaturePoint i≤ s) :
    ‖finiteSpectral (coefficientInput C a w) (waveFunctionJet 1 br 2 s)‖≤‖a‖*finiteCurvatureCap br i := by
  sorry
end AtomicTriangular.Construction
end

end OAI
end
