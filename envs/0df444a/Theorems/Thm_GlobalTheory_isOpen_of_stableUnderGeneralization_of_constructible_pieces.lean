-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_of_stableUnderGeneralization_of_constructible_pieces
-- name    : GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:22.191696+00:00
-- url     : https://prove2.me/theorems/129ea963-855a-4258-a9ca-87ed40b1f6ef
-- title:
--   Global Theory: is Open of stable Under Generalization of constructible pieces
-- statement:
--   The Global Theory construction uses the is Open of stable Under Generalization of constructible pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfConstructible.lean#L30-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfConstructible.lean#L30-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfConstructible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.isOpen_of_stableUnderGeneralization_of_constructible_pieces :
    ∀ (A : Type) [CommRing A] (Z : Set (PrimeSpectrum A)), StableUnderGeneralization Z → (∀ p ∈ Z, ∃ (a : A) (I : Finset A), a ∉ p.asIdeal ∧ (∀ c ∈ I, c ∈ p.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → t ∈ Z) → IsOpen Z := by sorry
