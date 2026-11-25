-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_expChartUnits_symm_apply
-- name    : GroundTheory.Automorphic.expChartUnits_symm_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:36.95907+00:00
-- url     : https://prove2.me/theorems/9e323cd8-0ad5-5feb-aaca-425b71b74769
-- title:
--   Automorphic: exp Chart Units symm apply
-- statement:
--   The Automorphic construction uses the exp Chart Units symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L129-L130

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
variable (𝕂 : Type*) [RCLike 𝕂] {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]
local notation "𝔢" => expPartialHomeomorph 𝕂 𝔸

theorem GroundTheory.Automorphic.expChartUnits_symm_apply (g : 𝔸ˣ) (X : 𝔸) :
    (((expChartUnits 𝕂 g).symm X : 𝔸ˣ) : 𝔸) = g * exp X := by sorry
