-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_expChartUnits_mem_maximalAtlas
-- name    : GroundTheory.Automorphic.expChartUnits_mem_maximalAtlas
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:16.589831+00:00
-- url     : https://prove2.me/theorems/c3025f4b-e077-4b5c-86a6-0279eaf05f1a
-- title:
--   Automorphic: exp Chart Units mem maximal Atlas
-- statement:
--   The Automorphic construction uses the exp Chart Units mem maximal Atlas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L132-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RealGroupsLie.lean#L132-L166

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

theorem GroundTheory.Automorphic.expChartUnits_mem_maximalAtlas (g : 𝔸ˣ) (n : WithTop ℕ∞) :
    expChartUnits 𝕂 g ∈ IsManifold.maximalAtlas 𝓘(𝕂, 𝔸) n 𝔸ˣ := by sorry
