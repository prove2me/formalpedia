-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompl_skewPart_hermPart
-- name    : GroundTheory.Automorphic.isCompl_skewPart_hermPart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:59.914257+00:00
-- url     : https://prove2.me/theorems/23ab907d-47e9-438a-bbcc-d8580cd99b3e
-- title:
--   Automorphic: is Compl skew Part herm Part
-- statement:
--   The Automorphic construction uses the is Compl skew Part herm Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L112-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L112-L142

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
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}

theorem GroundTheory.Automorphic.isCompl_skewPart_hermPart (hstar : ∀ X ∈ L, Xᴴ ∈ L) :
    IsCompl (skewPart L) (hermPart L) := by sorry
