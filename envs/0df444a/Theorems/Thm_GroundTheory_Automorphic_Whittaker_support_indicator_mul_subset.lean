-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_support_indicator_mul_subset
-- name    : GroundTheory.Automorphic.Whittaker.support_indicator_mul_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:02.172111+00:00
-- url     : https://prove2.me/theorems/41fb9544-8682-43a9-80c7-82122528ce8d
-- title:
--   Whittaker: support indicator mul subset
-- statement:
--   The Whittaker construction uses the support indicator mul subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L69-L74

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
omit [TopologicalSpace X]

theorem GroundTheory.Automorphic.Whittaker.support_indicator_mul_subset {A : Set X} {f : X → ℂ} :
    Function.support (fun x => A.indicator 1 x * f x) ⊆ A ∩ Function.support f := by sorry
