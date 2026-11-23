-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCohomologyFunctor_map_tateZeroClass
-- name    : GroundTheory.GroupCoh.tateCohomologyFunctor_map_tateZeroClass
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:39.105803+00:00
-- url     : https://prove2.me/theorems/e3e6e1f6-38f1-44be-a981-05442eda6351
-- title:
--   Group Coh: tate Cohomology Functor map tate Zero Class
-- statement:
--   The Group Coh construction uses the tate Cohomology Functor map tate Zero Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateZeroClass.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateZeroClass.lean#L42-L46

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.tateCohomologyFunctor_map_tateZeroClass {M N : Rep.{u} k G} (φ : M ⟶ N)
    (x : M.ρ.invariants) :
    ((tateCohomologyFunctor 0).map φ).hom (tateZeroClass M x) =
      tateZeroClass N (((Rep.invariantsFunctor k G).map φ).hom x) := by sorry
