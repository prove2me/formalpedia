-- Prove2me | Theorems.Thm_OAI_KadisonKastler_tomiyama_map_projection_mul
-- name    : OAI.KadisonKastler.tomiyama_map_projection_mul
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:37:50.544695+00:00
-- url     : https://prove2.me/theorems/25d5ac85-8dc2-45e5-a27c-9f1d99c878ea
-- title:
--   OAI.KadisonKastler.tomiyama_map_projection_mul: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.tomiyama_map_projection_mul` of [lean/OAI/Analysis/KadisonKastler/TomiyamaBimodule.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomiyamaBimodule.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem tomiyama_map_projection_mul (e : B) (he : IsStarProjection e) (x : A) :
--       P (φ e * x) = e * P x
--   ```
--
--   **Used by.** The proofs of `OAI.KadisonKastler.constructedStabilityCoreInputs`, `OAI.KadisonKastler.expectedMatrixSubfactorModel_of_centralizing_stages` and `OAI_KadisonKastler_publishedFieldTomiyama` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomiyamaBimodule.lean (declaration OAI.KadisonKastler.tomiyama_map_projection_mul)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Module

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hP hfix

theorem tomiyama_map_projection_mul (e : B) (he : IsStarProjection e) (x : A) :
    P (φ e * x) = e * P x := by
  sorry

end

end KadisonKastler

end OAI
end
