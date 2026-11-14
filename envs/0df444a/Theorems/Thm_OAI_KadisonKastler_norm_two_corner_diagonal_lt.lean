-- Prove2me | Theorems.Thm_OAI_KadisonKastler_norm_two_corner_diagonal_lt
-- name    : OAI.KadisonKastler.norm_two_corner_diagonal_lt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:16.315715+00:00
-- url     : https://prove2.me/theorems/95e5f10e-695e-46fb-9dfb-bcc824ef4f0a
-- title:
--   OAI.KadisonKastler.norm_two_corner_diagonal_lt: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.norm_two_corner_diagonal_lt` of [lean/OAI/Analysis/KadisonKastler/TwoCornerStrictContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TwoCornerStrictContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem norm_two_corner_diagonal_lt (p T : A) (hp : IsStarProjection p)
--       (hT : IsSelfAdjoint T) (ε : ℝ) (hε : 0 < ε) (hεT : ε ≤ ‖T‖)
--       (hpq : ε ^ 2 • p ≤ star ((1 - p) * (T * p)) * ((1 - p) * (T * p)))
--       (hqp : ε ^ 2 • (1 - p) ≤ star (p * (T * (1 - p))) * (p * (T * (1 - p)))) :
--       ‖p * T * p + (1 - p) * T * (1 - p)‖ < ‖T‖
--   ```
--
--   **Used by.** The proof of `OAI.KadisonKastler.CuntzFamily.upperRight_eq_zero_of_typeIII_constantNorm_of_projection_countability` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/TwoCornerStrictContraction.lean (declaration OAI.KadisonKastler.norm_two_corner_diagonal_lt)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
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

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_two_corner_diagonal_lt (p T : A) (hp : IsStarProjection p)
    (hT : IsSelfAdjoint T) (ε : ℝ) (hε : 0 < ε) (hεT : ε ≤ ‖T‖)
    (hpq : ε ^ 2 • p ≤ star ((1 - p) * (T * p)) * ((1 - p) * (T * p)))
    (hqp : ε ^ 2 • (1 - p) ≤ star (p * (T * (1 - p))) * (p * (T * (1 - p)))) :
    ‖p * T * p + (1 - p) * T * (1 - p)‖ < ‖T‖ := by
  sorry

end

end KadisonKastler

end OAI
end
