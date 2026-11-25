-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateRes_app_comp_tateCores_app
-- name    : GroundTheory.GroupCoh.tateRes_app_comp_tateCores_app
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:28:37.273976+00:00
-- url     : https://prove2.me/theorems/8d6df195-02e8-5100-be40-a4691ce7684b
-- title:
--   Group Coh: tate Res app comp tate Cores app
-- statement:
--   The Group Coh construction uses the tate Res app comp tate Cores app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L71-L76

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

theorem GroundTheory.GroupCoh.tateRes_app_comp_tateCores_app (A : Rep.{u} k G) (n : ℤ) :
    (tateRes S n).app A ≫ (tateCores S n).app A = S.index • 𝟙 (tateCohomology A n) := by sorry
