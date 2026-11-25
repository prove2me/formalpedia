-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_IsTateDelta_comp
-- name    : GroundTheory.GroupCoh.IsTateDelta.comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:07.734849+00:00
-- url     : https://prove2.me/theorems/1b9ee408-cc2e-5051-85d5-19117b7adc46
-- title:
--   Is Tate Delta: comp
-- statement:
--   The Is Tate Delta construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L68-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateSubgroupMaps.lean#L68-L74

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

theorem GroundTheory.GroupCoh.IsTateDelta.comp {α : ∀ n : ℤ, resFunctor U.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor V.subtype ⋙ tateCohomologyFunctor n}
    {β : ∀ n : ℤ, resFunctor V.subtype ⋙ tateCohomologyFunctor (R := k) n ⟶
      resFunctor W.subtype ⋙ tateCohomologyFunctor n}
    (hα : IsTateDelta α) (hβ : IsTateDelta β) : IsTateDelta (fun n => α n ≫ β n) := by sorry
