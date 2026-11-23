-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_indicator_mul_mem
-- name    : GroundTheory.Automorphic.Whittaker.indicator_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:35.497901+00:00
-- url     : https://prove2.me/theorems/6aa78809-0630-4413-8300-d07c4f226584
-- title:
--   Whittaker: indicator mul mem
-- statement:
--   The Whittaker construction uses the indicator mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L54-L66

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

theorem GroundTheory.Automorphic.Whittaker.indicator_mul_mem {U A : Set X} (hA : IsClopen A) {f : X → ℂ}
    (hf : f ∈ supportedIn U) : (fun x => A.indicator 1 x * f x) ∈ supportedIn U := by sorry
