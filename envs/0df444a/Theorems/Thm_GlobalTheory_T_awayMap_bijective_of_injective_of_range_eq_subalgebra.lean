-- Prove2me | Theorems.Thm_GlobalTheory_T_awayMap_bijective_of_injective_of_range_eq_subalgebra
-- name    : GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:27:04.526155+00:00
-- url     : https://prove2.me/theorems/da7d7044-b821-4a50-8d3f-8fce9e36219f
-- title:
--   T: away Map bijective of injective of range eq subalgebra
-- statement:
--   The T construction uses the away Map bijective of injective of range eq subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapBijectiveOfRangeEqSubalgebraStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapBijectiveOfRangeEqSubalgebraStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by sorry
