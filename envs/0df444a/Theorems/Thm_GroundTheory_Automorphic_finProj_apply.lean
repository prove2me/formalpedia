-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_finProj_apply
-- name    : GroundTheory.Automorphic.finProj_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:56.852795+00:00
-- url     : https://prove2.me/theorems/ef6e0973-e510-47cc-b0e4-233c3e59ebec
-- title:
--   Automorphic: fin Proj apply
-- statement:
--   The Automorphic construction uses the fin Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L19-L20

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

theorem GroundTheory.Automorphic.finProj_apply (u : ι → H) (x : H) : finProj u x = ∑ i, ⟪u i, x⟫_ℂ • u i := by sorry
