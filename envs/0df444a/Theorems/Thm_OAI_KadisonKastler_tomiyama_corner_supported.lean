-- Prove2me | Theorems.Thm_OAI_KadisonKastler_tomiyama_corner_supported
-- name    : OAI.KadisonKastler.tomiyama_corner_supported
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:37:50.556458+00:00
-- url     : https://prove2.me/theorems/03df527c-d6e0-4fa7-ae23-cf056c85d420
-- title:
--   OAI.KadisonKastler.tomiyama_corner_supported: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.tomiyama_corner_supported` of [lean/OAI/Analysis/KadisonKastler/TomiyamaProjection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomiyamaProjection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem tomiyama_corner_supported (e : B) (he : IsStarProjection e) (x : A) :
--       e * P (φ e * x * φ e) * e = P (φ e * x * φ e)
--   ```
--
--   **Used by.** The proof of `OAI.KadisonKastler.tomiyama_map_projection_mul` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TomiyamaProjection.lean (declaration OAI.KadisonKastler.tomiyama_corner_supported)

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

local instance tomiyamaProjectionSourceOrder_re23722_1 : PartialOrder A := CStarAlgebra.spectralOrder A
local instance tomiyamaProjectionSourceStarOrder_re23722_1 : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
local instance tomiyamaProjectionTargetOrder_re23722_1 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance tomiyamaProjectionTargetStarOrder_re23722_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
variable (φ : B →⋆ₐ[ℂ] A) (P : A →L[ℂ] B)
  (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hfix : ∀ b, P (φ b) = b)

include hP hfix

theorem tomiyama_corner_supported (e : B) (he : IsStarProjection e) (x : A) :
    e * P (φ e * x * φ e) * e = P (φ e * x * φ e) := by
  sorry

end

end KadisonKastler

end OAI
end
