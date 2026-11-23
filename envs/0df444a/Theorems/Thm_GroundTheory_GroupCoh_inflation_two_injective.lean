-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_inflation_two_injective
-- name    : GroundTheory.GroupCoh.inflation_two_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:13.906504+00:00
-- url     : https://prove2.me/theorems/f088cc3f-467e-4e3d-a147-042e5fa78589
-- title:
--   Group Coh: inflation two injective
-- statement:
--   The Group Coh construction uses the inflation two injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L171-L175

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

theorem GroundTheory.GroupCoh.inflation_two_injective (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    Function.Injective (inflation A S 2).hom := by sorry
