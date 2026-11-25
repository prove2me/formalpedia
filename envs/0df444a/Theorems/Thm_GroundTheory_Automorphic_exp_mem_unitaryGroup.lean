-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exp_mem_unitaryGroup
-- name    : GroundTheory.Automorphic.exp_mem_unitaryGroup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:21.179842+00:00
-- url     : https://prove2.me/theorems/94c51030-e856-4f11-8eb7-ca378ff83227
-- title:
--   Automorphic: exp mem unitary Group
-- statement:
--   The Automorphic construction uses the exp mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L288-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L288-L292

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.exp_mem_unitaryGroup {X : Matrix ι ι 𝕜} (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup ι 𝕜 := by sorry
