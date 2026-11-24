-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_iff_of_shortExact_of_finite
-- name    : GroundTheory.GroupCoh.hasHerbrandQuotient_iff_of_shortExact_of_finite
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:21.240187+00:00
-- url     : https://prove2.me/theorems/83dafdea-1063-4208-882c-9fde27c76cd2
-- title:
--   Group Coh: has Herbrand Quotient iff of short Exact of finite
-- statement:
--   The Group Coh construction uses the has Herbrand Quotient iff of short Exact of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L407-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L407-L415

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

theorem GroundTheory.GroupCoh.hasHerbrandQuotient_iff_of_shortExact_of_finite [Finite C] (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    HasHerbrandQuotient fA gA ↔ HasHerbrandQuotient fB gB := by sorry
