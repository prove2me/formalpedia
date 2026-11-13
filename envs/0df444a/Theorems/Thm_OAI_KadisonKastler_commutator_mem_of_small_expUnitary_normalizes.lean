-- Prove2me | Theorems.Thm_OAI_KadisonKastler_commutator_mem_of_small_expUnitary_normalizes
-- name    : OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:37:47.378336+00:00
-- url     : https://prove2.me/theorems/0bd10ff3-0290-466f-a85a-b8fda329df5e
-- title:
--   OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes` of [lean/OAI/Analysis/KadisonKastler/NormalizerLogarithm.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/NormalizerLogarithm.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`):
--
--   ```lean
--   theorem commutator_mem_of_small_expUnitary_normalizes
--       (P : VonNeumannAlgebra H) (h : selfAdjoint (H →L[ℂ] H))
--       (hsmall : ‖(h : H →L[ℂ] H)‖ ≤ 1 / 32)
--       (hnormalizes : Conjugates (H := H) (selfAdjoint.expUnitary h) P P) :
--       ∀ a ∈ P, (h : H →L[ℂ] H) * a - a * (h : H →L[ℂ] H) ∈ P
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.Conjugates` (the published bundle `Def_StrongKadisonKastler`).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_small_normalizer_log` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/NormalizerLogarithm.lean (declaration OAI.KadisonKastler.commutator_mem_of_small_expUnitary_normalizes)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.MetricSpace.Contracting
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

theorem commutator_mem_of_small_expUnitary_normalizes
    (P : VonNeumannAlgebra H) (h : selfAdjoint (H →L[ℂ] H))
    (hsmall : ‖(h : H →L[ℂ] H)‖ ≤ 1 / 32)
    (hnormalizes : Conjugates (H := H) (selfAdjoint.expUnitary h) P P) :
    ∀ a ∈ P, (h : H →L[ℂ] H) * a - a * (h : H →L[ℂ] H) ∈ P := by
  sorry

end

end KadisonKastler

end OAI
end
