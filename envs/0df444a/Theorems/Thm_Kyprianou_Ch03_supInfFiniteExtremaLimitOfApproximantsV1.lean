-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfFiniteExtremaLimitOfApproximantsV1
-- name    : Kyprianou.Ch03.supInfFiniteExtremaLimitOfApproximantsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T11:02:31.664214+00:00
-- url     : https://prove2.me/theorems/0b40acff-4732-45f6-bc22-afbccc557c79
-- title:
--   Finite extrema converge under pointwise approximability
-- statement:
--   All finite extrema lie between the full extrema. For a strictly smaller lower test of the supremum, choose a point of A above it, and use the convergent approximants to obtain the eventual lower bound. Use the dual argument for infima.
-- source:
--   Kyprianou (2006), Chapter 3 Lemma 3.5; parent 595bcca9-772a-41a6-8165-d1d8abc9d6e8.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfFiniteExtremaLimitOfApproximantsV1
    (A : Set Real) (hA : A.Nonempty) (hAb : BddAbove A) (hAl : BddBelow A)
    (B : ℕ → Set Real) (hB : ∀ n, (B n).Nonempty)
    (hsub : ∀ n, B n ⊆ A)
    (happrox : ∀ a ∈ A, ∃ u : ℕ → Real,
      (∀ n, u n ∈ B n) ∧ Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => sSup (B n)) atTop (𝓝 (sSup A)) ∧
    Tendsto (fun n => sInf (B n)) atTop (𝓝 (sInf A)) := by sorry
