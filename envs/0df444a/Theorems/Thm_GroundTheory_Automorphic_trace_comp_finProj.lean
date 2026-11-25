-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_trace_comp_finProj
-- name    : GroundTheory.Automorphic.trace_comp_finProj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:28.99711+00:00
-- url     : https://prove2.me/theorems/5f269c10-1d03-4c49-bf9f-fddfac662736
-- title:
--   Automorphic: trace comp fin Proj
-- statement:
--   The Automorphic construction uses the trace comp fin Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L65-L67

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

theorem GroundTheory.Automorphic.trace_comp_finProj [CompleteSpace H] (u : ι → H) (S : H →L[ℂ] H) :
    trace (S.comp (finProj u)) = ∑ i, ⟪u i, S (u i)⟫_ℂ := by sorry
