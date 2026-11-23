-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_TateAcyclic_of_iso
-- name    : GroundTheory.GroupCoh.TateAcyclic.of_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:24.776455+00:00
-- url     : https://prove2.me/theorems/6df73b89-d7d8-483f-a3e1-57e5e497af68
-- title:
--   Tate Acyclic: of iso
-- statement:
--   The Tate Acyclic construction uses the of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
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
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.TateAcyclic.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M := by sorry
