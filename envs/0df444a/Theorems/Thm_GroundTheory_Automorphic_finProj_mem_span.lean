-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_finProj_mem_span
-- name    : GroundTheory.Automorphic.finProj_mem_span
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:06.216233+00:00
-- url     : https://prove2.me/theorems/311f1702-5bf4-4a51-8058-d878fd7511d9
-- title:
--   Automorphic: fin Proj mem span
-- statement:
--   The Automorphic construction uses the fin Proj mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceNormComp
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]

theorem GroundTheory.Automorphic.finProj_mem_span (u : ι → H) (x : H) : finProj u x ∈ Submodule.span ℂ (Set.range u) := by sorry
