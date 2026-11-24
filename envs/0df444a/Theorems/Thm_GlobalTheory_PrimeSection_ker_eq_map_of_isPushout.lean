-- Prove2me | Theorems.Thm_GlobalTheory_PrimeSection_ker_eq_map_of_isPushout
-- name    : GlobalTheory.PrimeSection.ker_eq_map_of_isPushout
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:43:45.938488+00:00
-- url     : https://prove2.me/theorems/ca27ba43-6c6b-4102-8264-6652757829d2
-- title:
--   Prime Section: ker eq map of is Pushout
-- statement:
--   The Prime Section construction uses the ker eq map of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L207-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueZpowMulAppLE.lean#L207-L224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection

theorem GlobalTheory.PrimeSection.ker_eq_map_of_isPushout {A B C P : CommRingCat.{u}} {α : A ⟶ B} {β : A ⟶ C} {γ : B ⟶ P}
    {δ : C ⟶ P} (h : IsPushout α β γ δ) (hβ : Function.Surjective β) :
    RingHom.ker γ.hom = (RingHom.ker β.hom).map α.hom := by sorry
