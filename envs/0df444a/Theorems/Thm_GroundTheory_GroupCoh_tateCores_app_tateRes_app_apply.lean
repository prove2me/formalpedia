-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCores_app_tateRes_app_apply
-- name    : GroundTheory.GroupCoh.tateCores_app_tateRes_app_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:19.129649+00:00
-- url     : https://prove2.me/theorems/bed729b6-eaca-4de7-b18f-f7bf9eba0cf4
-- title:
--   Group Coh: tate Cores app tate Res app apply
-- statement:
--   The Group Coh construction uses the tate Cores app tate Res app apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateResEqZeroOfNsmulEqZero.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateResEqZeroOfNsmulEqZero.lean#L13-L17

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateResEqZeroOfNsmulEqZero
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
open CategoryTheory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.tateCores_app_tateRes_app_apply (S : Subgroup G) [Fintype S] (A : Rep.{u} k G) (n : ℤ)
    (x : tateCohomology A n) :
    ((tateCores S n).app A).hom (((tateRes S n).app A).hom x) = S.index • x := by sorry
