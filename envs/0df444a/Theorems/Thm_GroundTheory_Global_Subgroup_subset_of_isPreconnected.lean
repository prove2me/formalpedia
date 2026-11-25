-- Prove2me | Theorems.Thm_GroundTheory_Global_Subgroup_subset_of_isPreconnected
-- name    : GroundTheory.Global.Subgroup.subset_of_isPreconnected
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:23:11.185691+00:00
-- url     : https://prove2.me/theorems/10d87cab-1f82-42fc-9423-0293858ba12d
-- title:
--   Subgroup: subset of is Preconnected
-- statement:
--   The Subgroup construction uses the subset of is Preconnected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/OpenSubgroup.lean#L11-L14

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section

theorem GroundTheory.Global.Subgroup.subset_of_isPreconnected {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {s : Set G}
    (hs : IsPreconnected s) (h1 : (1 : G) ∈ s) : s ⊆ H := by sorry
