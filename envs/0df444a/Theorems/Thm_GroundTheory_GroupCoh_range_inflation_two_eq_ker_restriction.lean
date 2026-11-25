-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_range_inflation_two_eq_ker_restriction
-- name    : GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:01.119948+00:00
-- url     : https://prove2.me/theorems/b03610e4-1a34-4cd2-8633-500ea4c1e9b7
-- title:
--   Group Coh: range inflation two eq ker restriction
-- statement:
--   The Group Coh construction uses the range inflation two eq ker restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L177-L182

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
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
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
variable {A S}

theorem GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction
    (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    LinearMap.range (inflation A S 2).hom = LinearMap.ker (restriction A S 2).hom := by sorry
