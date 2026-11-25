-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateIndIso_inv_eq
-- name    : GroundTheory.GroupCoh.tateIndIso_inv_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:29:58.194116+00:00
-- url     : https://prove2.me/theorems/63835282-dca4-4322-a3ca-2c7db2b47825
-- title:
--   Group Coh: tate Ind Iso inv eq
-- statement:
--   The Group Coh construction uses the tate Ind Iso inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L66-L69

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
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
open CategoryTheory Limits Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G] (S : Subgroup G) [Fintype S]
open scoped Classical

theorem GroundTheory.GroupCoh.tateIndIso_inv_eq (B : Rep.{u} k S) (n : ℤ) :
    (tateIndIso S B n).inv =
      (tateCoindIso S B n).inv ≫ (tateCohomologyFunctor n).map (indCoindIso.{u, u, u} B).inv := by sorry
