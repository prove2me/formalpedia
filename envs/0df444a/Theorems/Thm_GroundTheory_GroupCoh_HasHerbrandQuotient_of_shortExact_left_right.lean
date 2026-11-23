-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_HasHerbrandQuotient_of_shortExact_left_right
-- name    : GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_left_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:38.478683+00:00
-- url     : https://prove2.me/theorems/c3405b61-34fa-4555-bf88-41f00151ee61
-- title:
--   Has Herbrand Quotient: of short Exact left right
-- statement:
--   The Has Herbrand Quotient construction uses the of short Exact left right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L351-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L351-L361

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

theorem GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_left_right (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hA : HasHerbrandQuotient fA gA) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fB gB := by sorry
