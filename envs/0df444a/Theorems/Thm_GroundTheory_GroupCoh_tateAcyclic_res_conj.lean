-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_res_conj
-- name    : GroundTheory.GroupCoh.tateAcyclic_res_conj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:54.997358+00:00
-- url     : https://prove2.me/theorems/79642c8a-a656-5b0c-aea1-e2b2350ab30d
-- title:
--   Group Coh: tate Acyclic res conj
-- statement:
--   The Group Coh construction uses the tate Acyclic res conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L121-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateGroupIso.lean#L121-L142

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialBasic
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateGroupIso
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

theorem GroundTheory.GroupCoh.tateAcyclic_res_conj {A : Rep.{u} k G} (U V : Subgroup G) [Fintype U] [Fintype V] (g : G)
    (hUV : ∀ x, x ∈ U ↔ g⁻¹ * x * g ∈ V) (hV : TateAcyclic (res V.subtype A)) :
    TateAcyclic (res U.subtype A) := by sorry
