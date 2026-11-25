-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_HasHerbrandQuotient_of_shortExact_mid_right
-- name    : GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_mid_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:34.392405+00:00
-- url     : https://prove2.me/theorems/ef2c4555-0985-4dc2-9a7e-79254da86992
-- title:
--   Has Herbrand Quotient: of short Exact mid right
-- statement:
--   The Has Herbrand Quotient construction uses the of short Exact mid right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L375-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L375-L385

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

theorem GroundTheory.GroupCoh.HasHerbrandQuotient.of_shortExact_mid_right (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0)
    (hB : HasHerbrandQuotient fB gB) (hC : HasHerbrandQuotient fC gC) :
    HasHerbrandQuotient fA gA := by sorry
