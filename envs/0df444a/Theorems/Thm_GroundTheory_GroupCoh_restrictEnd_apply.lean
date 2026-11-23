-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- name    : GroundTheory.GroupCoh.restrictEnd_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:16.928391+00:00
-- url     : https://prove2.me/theorems/fadc81a0-3e3e-436d-9eaa-c4ff8e1b6fd7
-- title:
--   Group Coh: restrict End apply
-- statement:
--   The Group Coh construction uses the restrict End apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L501-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L501-L503

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

theorem GroundTheory.GroupCoh.restrictEnd_apply (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) (x : S) :
    (restrictEnd f S hS x : B) = f x := by sorry

attribute [defeq] GroundTheory.GroupCoh.restrictEnd_apply
