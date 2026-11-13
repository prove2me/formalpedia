-- Prove2me | Theorems.Thm_OAI_KadisonKastler_norm_expUnitary_conjugation_remainder_le
-- name    : OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:37:42.34197+00:00
-- url     : https://prove2.me/theorems/e5ad1b24-480a-45c1-ac47-1b3fb5c27588
-- title:
--   OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le` of [lean/OAI/Analysis/KadisonKastler/UnitaryExponentialBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/UnitaryExponentialBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem norm_expUnitary_conjugation_remainder_le
--       (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) :
--       ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x -
--         (Complex.I • ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)) : H →L[ℂ] H)‖ ≤
--           4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.unitaryConj` (the published bundle `Def_StrongKadisonKastler`).
--
--   **Used by.** The proof of `OAI.KadisonKastler.normalizer_distance_quadratic` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/UnitaryExponentialBounds.lean (declaration OAI.KadisonKastler.norm_expUnitary_conjugation_remainder_le)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem norm_expUnitary_conjugation_remainder_le
    (h : selfAdjoint (H →L[ℂ] H)) (x : H →L[ℂ] H) :
    ‖unitaryConj (H := H) (selfAdjoint.expUnitary h) x - x -
      (Complex.I • ((h : H →L[ℂ] H) * x - x * (h : H →L[ℂ] H)) : H →L[ℂ] H)‖ ≤
        4 * ‖(h : H →L[ℂ] H)‖ ^ 2 * ‖x‖ := by
  sorry

end

end KadisonKastler

end OAI
end
