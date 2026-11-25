-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_linearYonedaObjMap_f_apply
-- name    : GroundTheory.GroupCoh.linearYonedaObjMap_f_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:24.769693+00:00
-- url     : https://prove2.me/theorems/56728ad3-2dcd-463e-a872-73ffaecbe66e
-- title:
--   Group Coh: linear Yoneda Obj Map f apply
-- statement:
--   The Group Coh construction uses the linear Yoneda Obj Map f apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L19-L20

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DiagonalSuccIsoFreeInvSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology Rep
universe v w u
variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

theorem GroundTheory.GroupCoh.linearYonedaObjMap_f_apply {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) (n : ℕ)
    (x : Y.X n ⟶ B) : (linearYonedaObjMap (R := R) f B).f n x = f.f n ≫ x := by sorry
