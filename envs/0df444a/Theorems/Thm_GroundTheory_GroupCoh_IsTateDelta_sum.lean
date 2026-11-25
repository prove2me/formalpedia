-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_IsTateDelta_sum
-- name    : GroundTheory.GroupCoh.IsTateDelta.sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:39.436037+00:00
-- url     : https://prove2.me/theorems/78284ec4-04b1-4927-bd9c-27f1b6315c5a
-- title:
--   Is Tate Delta: sum
-- statement:
--   The Is Tate Delta construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L78-L84

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_TateUnique
import Definitions.Def_GroundTheory_TateCohomology_TateTransport
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
import Definitions.Def_GroundTheory_TateCohomology_TateSubgroupMaps
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
variable [Fintype G]
open GroundTheory.GroupCoh.IsTateDelta
variable {U V W : Subgroup G} [Fintype U] [Fintype V] [Fintype W]
omit [Fintype G]

theorem GroundTheory.GroupCoh.IsTateDelta.sum {ι : Type*} (s : Finset ι)
    {α : ι → ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : ∀ i ∈ s, IsTateDelta (α i)) : IsTateDelta (fun n => ∑ i ∈ s, α i n) := by sorry
