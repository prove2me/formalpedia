-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_indicator_mem_locallyConstantCompactSupport
-- name    : GroundTheory.Automorphic.indicator_mem_locallyConstantCompactSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:21.744959+00:00
-- url     : https://prove2.me/theorems/af9f1577-8244-4533-b91a-d8e79b145263
-- title:
--   Automorphic: indicator mem locally Constant Compact Support
-- statement:
--   The Automorphic construction uses the indicator mem locally Constant Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L30-L34

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

theorem GroundTheory.Automorphic.indicator_mem_locallyConstantCompactSupport [T2Space X] {U : Set X} (hc : IsCompact U)
    (ho : IsOpen U) (e : E) :
    U.indicator (fun _ => e) ∈ locallyConstantCompactSupport X R E := by sorry
