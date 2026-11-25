-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_valuation_eq_of_isEquiv
-- name    : GroundTheory.FunctionField.valuation_eq_of_isEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:30.600792+00:00
-- url     : https://prove2.me/theorems/b76647b0-8557-45ab-934a-221890d5a962
-- title:
--   Function Field: valuation eq of is Equiv
-- statement:
--   The Function Field construction uses the valuation eq of is Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceSum.lean#L10-L42

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero

theorem GroundTheory.FunctionField.valuation_eq_of_isEquiv {F : Type*} [Field F] {v₁ v₂ : Valuation F ℤᵐ⁰}
    (h : v₁.IsEquiv v₂) (h₁ : Function.Surjective v₁) (h₂ : Function.Surjective v₂) : v₁ = v₂ := by sorry
