-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_HasHerbrandQuotient_of_shortExact_left_mid
-- name    : GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_left_mid
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:48.71037+00:00
-- url     : https://prove2.me/theorems/031ffe2a-d9e8-47ac-8d5c-fca49da8cba0
-- title:
--   Has Herbrand Quotient: of short Exact left mid
-- statement:
--   The Has Herbrand Quotient construction uses the of short Exact left mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L363-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L363-L373

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}

theorem GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_left_mid (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hB : HasHerbrandQuotient fB gB) :
    HasHerbrandQuotient fC gC := by sorry
