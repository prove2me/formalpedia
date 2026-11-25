-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_IsTateDelta_ext
-- name    : GroundTheory.GroupCoh.IsTateDelta.ext
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:09:27.208928+00:00
-- url     : https://prove2.me/theorems/a9dfeb5b-1d13-5778-a4f8-8e207f96dd67
-- title:
--   Is Tate Delta: ext
-- statement:
--   The Is Tate Delta construction uses the ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L54-L59

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

theorem GroundTheory.GroupCoh.IsTateDelta.ext {α β : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) (h0 : α 0 = β 0) : α = β := by sorry
