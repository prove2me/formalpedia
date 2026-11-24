-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_herbrandQuotient_restrictEnd
-- name    : GroundTheory.GroupCoh.herbrandQuotient_restrictEnd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:09.122355+00:00
-- url     : https://prove2.me/theorems/0c3cdbff-7ad2-4428-91f2-08d9969b5acd
-- title:
--   Group Coh: herbrand Quotient restrict End
-- statement:
--   The Group Coh construction uses the herbrand Quotient restrict End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L513-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L513-L519

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

theorem GroundTheory.GroupCoh.herbrandQuotient_restrictEnd {f g : B →+ B} (S : AddSubgroup B) [S.FiniteIndex]
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S) (hfg : ∀ b, f (g b) = 0)
    (hgf : ∀ b, g (f b) = 0) :
    herbrandQuotient (restrictEnd f S hfS) (restrictEnd g S hgS) = herbrandQuotient f g := by sorry
