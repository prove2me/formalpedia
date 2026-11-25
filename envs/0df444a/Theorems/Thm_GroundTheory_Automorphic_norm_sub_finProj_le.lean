-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_norm_sub_finProj_le
-- name    : GroundTheory.Automorphic.norm_sub_finProj_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:40.595122+00:00
-- url     : https://prove2.me/theorems/38950ac9-2792-4caf-8cb4-9324ba6a9f4c
-- title:
--   Automorphic: norm sub fin Proj le
-- statement:
--   The Automorphic construction uses the norm sub fin Proj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L40-L49

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

theorem GroundTheory.Automorphic.norm_sub_finProj_le (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ‖x - finProj u x‖ ≤ ‖x - g‖ := by sorry
