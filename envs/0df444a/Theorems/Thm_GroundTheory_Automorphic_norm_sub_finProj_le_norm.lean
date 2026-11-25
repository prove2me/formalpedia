-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_norm_sub_finProj_le_norm
-- name    : GroundTheory.Automorphic.norm_sub_finProj_le_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:12:10.191616+00:00
-- url     : https://prove2.me/theorems/375a2839-6273-452b-98ba-3f3afaf972a3
-- title:
--   Automorphic: norm sub fin Proj le norm
-- statement:
--   The Automorphic construction uses the norm sub fin Proj le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L51-L52

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

theorem GroundTheory.Automorphic.norm_sub_finProj_le_norm (hu : Orthonormal ℂ u) (x : H) : ‖x - finProj u x‖ ≤ ‖x‖ := by sorry
