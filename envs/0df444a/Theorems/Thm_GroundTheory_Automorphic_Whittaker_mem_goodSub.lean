-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_goodSub
-- name    : GroundTheory.Automorphic.Whittaker.mem_goodSub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:04.850111+00:00
-- url     : https://prove2.me/theorems/603b54d4-f40c-4b49-be3a-73fde90d79d9
-- title:
--   Whittaker: mem good Sub
-- statement:
--   The Whittaker construction uses the mem good Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L127-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L127-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.mem_goodSub {f : GL (Fin n) F → ℂ} : f ∈ goodSub n ψ₀ ↔ f - sigmaL f ∈ rel n ψ₀ := by sorry
