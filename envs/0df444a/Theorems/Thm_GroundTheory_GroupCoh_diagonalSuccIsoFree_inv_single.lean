-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_diagonalSuccIsoFree_inv_single
-- name    : GroundTheory.GroupCoh.diagonalSuccIsoFree_inv_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:26.851805+00:00
-- url     : https://prove2.me/theorems/44d7b53c-57c4-409d-9f86-33d19a15b6ce
-- title:
--   Group Coh: diagonal Succ Iso Free inv single
-- statement:
--   The Group Coh construction uses the diagonal Succ Iso Free inv single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DiagonalSuccIsoFreeInvSingle.lean#L61-L81

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
variable {k G : Type u} [CommRing k] [Group G]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.GroupCoh.diagonalSuccIsoFree_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by sorry
