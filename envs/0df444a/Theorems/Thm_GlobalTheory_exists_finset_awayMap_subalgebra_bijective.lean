-- Prove2me | Theorems.Thm_GlobalTheory_exists_finset_awayMap_subalgebra_bijective
-- name    : GlobalTheory.exists_finset_awayMap_subalgebra_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:40.884138+00:00
-- url     : https://prove2.me/theorems/46269b3f-93c8-4fd1-9623-7a75c849ce3d
-- title:
--   Global Theory: exists finset away Map subalgebra bijective
-- statement:
--   The Global Theory construction uses the exists finset away Map subalgebra bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinsetAwayMapSubalgebraBijective.lean#L7-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinsetAwayMapSubalgebraBijective.lean#L7-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.exists_finset_awayMap_subalgebra_bijective :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B),
      (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) →
      ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C →
        ∀ b ∈ g, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by sorry
