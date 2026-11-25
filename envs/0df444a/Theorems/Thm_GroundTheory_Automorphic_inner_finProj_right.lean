-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_inner_finProj_right
-- name    : GroundTheory.Automorphic.inner_finProj_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:09.619816+00:00
-- url     : https://prove2.me/theorems/dee38776-aae6-4676-adc5-934baa97f836
-- title:
--   Automorphic: inner fin Proj right
-- statement:
--   The Automorphic construction uses the inner fin Proj right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L28-L31

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
variable {u : ι → H}

theorem GroundTheory.Automorphic.inner_finProj_right (hu : Orthonormal ℂ u) (x : H) (j : ι) :
    ⟪u j, finProj u x⟫_ℂ = ⟪u j, x⟫_ℂ := by sorry
