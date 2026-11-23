-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_KerModRange_mk_eq_mk_iff
-- name    : GroundTheory.GroupCoh.KerModRange.mk_eq_mk_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:46.822893+00:00
-- url     : https://prove2.me/theorems/97cc4d48-a29d-49e7-93ea-a4238bd0a405
-- title:
--   Ker Mod Range: mk eq mk iff
-- statement:
--   The Ker Mod Range construction uses the mk eq mk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L54-L57

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
variable {A : Type*} [AddCommGroup A]

theorem GroundTheory.GroupCoh.KerModRange.mk_eq_mk_iff {f g : A →+ A} (x y : f.ker) :
    (QuotientAddGroup.mk x : KerModRange f g) = QuotientAddGroup.mk y ↔
      (x : A) - y ∈ g.range := by sorry
