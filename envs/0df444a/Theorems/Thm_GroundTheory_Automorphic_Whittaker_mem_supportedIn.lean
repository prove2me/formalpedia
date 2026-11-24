-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_supportedIn
-- name    : GroundTheory.Automorphic.Whittaker.mem_supportedIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:11.073807+00:00
-- url     : https://prove2.me/theorems/de45d295-1e3f-4f0b-a524-20f31136a7c5
-- title:
--   Whittaker: mem supported In
-- statement:
--   The Whittaker construction uses the mem supported In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
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
open Set Topology
variable {X : Type*} [TopologicalSpace X]

theorem GroundTheory.Automorphic.Whittaker.mem_supportedIn {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U := by sorry
