-- Prove2me | Theorems.Thm_GlobalTheory_exists_isPrimitiveRoot_of_injective_character
-- name    : GlobalTheory.exists_isPrimitiveRoot_of_injective_character
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:25:08.166233+00:00
-- url     : https://prove2.me/theorems/796ee3b4-d55d-55e4-a839-5947a2252ae6
-- title:
--   Global Theory: exists is Primitive Root of injective character
-- statement:
--   The Global Theory construction uses the exists is Primitive Root of injective character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsIsPrimitiveRootOfInjectiveCharacter.lean#L5-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsIsPrimitiveRootOfInjectiveCharacter.lean#L5-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsIsPrimitiveRootOfInjectiveCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by sorry
