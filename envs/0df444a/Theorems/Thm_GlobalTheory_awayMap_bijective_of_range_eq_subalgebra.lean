-- Prove2me | Theorems.Thm_GlobalTheory_awayMap_bijective_of_range_eq_subalgebra
-- name    : GlobalTheory.awayMap_bijective_of_range_eq_subalgebra
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:42.547196+00:00
-- url     : https://prove2.me/theorems/8f63f9e2-d1e7-4469-a2f9-5258526171e5
-- title:
--   Global Theory: away Map bijective of range eq subalgebra
-- statement:
--   The Global Theory construction uses the away Map bijective of range eq subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapBijectiveOfRangeEqSubalgebra.lean#L6-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapBijectiveOfRangeEqSubalgebra.lean#L6-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory

theorem GlobalTheory.awayMap_bijective_of_range_eq_subalgebra :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by sorry
