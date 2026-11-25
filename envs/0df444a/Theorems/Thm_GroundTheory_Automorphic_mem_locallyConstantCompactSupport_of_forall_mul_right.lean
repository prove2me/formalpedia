-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_locallyConstantCompactSupport_of_forall_mul_right
-- name    : GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:47.219541+00:00
-- url     : https://prove2.me/theorems/1efa89c3-faaf-40bd-b3e0-286ebc2f1770
-- title:
--   Automorphic: mem locally Constant Compact Support of forall mul right
-- statement:
--   The Automorphic construction uses the mem locally Constant Compact Support of forall mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LocallyConstantCompact.lean#L74-L79

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
variable {G : Type*} [Group G] {E : Type*}
variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]

theorem GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right (K : OpenSubgroup G)
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f ∈ locallyConstantCompactSupport G R E := by sorry
