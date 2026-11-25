-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasSum_inner_comp_finProj
-- name    : GroundTheory.Automorphic.hasSum_inner_comp_finProj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:13.686809+00:00
-- url     : https://prove2.me/theorems/e91b9966-08ed-48d3-abc3-dc02e2e79027
-- title:
--   Automorphic: has Sum inner comp fin Proj
-- statement:
--   The Automorphic construction uses the has Sum inner comp fin Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceStrongLimit.lean#L54-L63

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

theorem GroundTheory.Automorphic.hasSum_inner_comp_finProj (u : ι → H) (S : H →L[ℂ] H) {κ : Type*}
    (b : HilbertBasis κ ℂ H) :
    HasSum (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) (∑ i, ⟪u i, S (u i)⟫_ℂ) := by sorry
