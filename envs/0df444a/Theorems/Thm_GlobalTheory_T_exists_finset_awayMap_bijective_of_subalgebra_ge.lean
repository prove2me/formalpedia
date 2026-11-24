-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_awayMap_bijective_of_subalgebra_ge
-- name    : GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:30.480632+00:00
-- url     : https://prove2.me/theorems/5cd521af-e6c6-48ca-8bae-ac5a282112ff
-- title:
--   T: exists finset away Map bijective of subalgebra ge
-- statement:
--   The T construction uses the exists finset away Map bijective of subalgebra ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinsetAwayMapSubalgebraBijectiveStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFinsetAwayMapSubalgebraBijectiveStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B), (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) → ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C → ∀ b ∈ g, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by sorry
