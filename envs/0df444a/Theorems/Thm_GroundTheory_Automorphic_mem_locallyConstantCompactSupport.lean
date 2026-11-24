-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_locallyConstantCompactSupport
-- name    : GroundTheory.Automorphic.mem_locallyConstantCompactSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:18.113234+00:00
-- url     : https://prove2.me/theorems/b322517e-8916-4ffb-b084-d17a6a744778
-- title:
--   Automorphic: mem locally Constant Compact Support
-- statement:
--   The Automorphic construction uses the mem locally Constant Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L26-L28

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
open scoped Pointwise
variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]
variable {X R E}

theorem GroundTheory.Automorphic.mem_locallyConstantCompactSupport {f : X → E} :
    f ∈ locallyConstantCompactSupport X R E ↔ IsLocallyConstant f ∧ HasCompactSupport f := by sorry
