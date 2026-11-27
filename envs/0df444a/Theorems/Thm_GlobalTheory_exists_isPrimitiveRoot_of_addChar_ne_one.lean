-- Prove2me | Theorems.Thm_GlobalTheory_exists_isPrimitiveRoot_of_addChar_ne_one
-- name    : GlobalTheory.exists_isPrimitiveRoot_of_addChar_ne_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:26:04.336646+00:00
-- url     : https://prove2.me/theorems/c84156f8-0308-491d-860d-415feccf788a
-- title:
--   Global Theory: exists is Primitive Root of add Char ne one
-- statement:
--   The Global Theory construction uses the exists is Primitive Root of add Char ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsIsPrimitiveRootOfAddCharNeOne.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsIsPrimitiveRootOfAddCharNeOne.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsIsPrimitiveRootOfAddCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_isPrimitiveRoot_of_addChar_ne_one :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by sorry
