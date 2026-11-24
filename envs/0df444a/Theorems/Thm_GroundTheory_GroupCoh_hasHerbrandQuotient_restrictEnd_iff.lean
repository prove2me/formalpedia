-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_hasHerbrandQuotient_restrictEnd_iff
-- name    : GroundTheory.GroupCoh.hasHerbrandQuotient_restrictEnd_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:08.088193+00:00
-- url     : https://prove2.me/theorems/a858990a-5fae-4cf8-a453-f5496d887a05
-- title:
--   Group Coh: has Herbrand Quotient restrict End iff
-- statement:
--   The Group Coh construction uses the has Herbrand Quotient restrict End iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L505-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L505-L511

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
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem GroundTheory.GroupCoh.hasHerbrandQuotient_restrictEnd_iff {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex]
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0)
    (hgf : ∀ b, g (f b) = 0) :
    HasHerbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) ↔ HasHerbrandQuotient f g := by sorry
