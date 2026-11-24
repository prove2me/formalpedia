-- Prove2me | Theorems.Thm_GlobalTheory_finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
-- name    : GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:46:32.417793+00:00
-- url     : https://prove2.me/theorems/96c0d249-914b-4fff-b420-814f6d35a4b3
-- title:
--   Global Theory: finite alg hom ker coker killed of onto mod ideal
-- statement:
--   The Global Theory construction uses the finite alg hom ker coker killed of onto mod ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitApproximationAdicCompletion.lean#L5-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitApproximationAdicCompletion.lean#L5-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitApproximationAdicCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finite_alg_hom_ker_coker_killed_of_onto_mod_ideal
    (A : Type) [CommRing A] [IsNoetherianRing A] (J : Ideal A) (M N : Type) [CommRing M]
    [Algebra A M] [Module.Finite A M] [CommRing N] [Algebra A N] [Module.Finite A N]
    (φ : M →ₐ[A] N) :
    (∀ y : N, ∃ t : M, y - φ t ∈ J.map (algebraMap A N)) →
    (∀ (n : ℕ) (t : M), φ t ∈ (J ^ n).map (algebraMap A N) → t ∈ (J ^ n).map (algebraMap A M)) →
    ∃ f : A, f - 1 ∈ J ∧ (∀ y : N, algebraMap A N f * y ∈ Set.range φ) ∧
      ∀ t : M, φ t = 0 → algebraMap A M f * t = 0 := by sorry
