-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_traceForm_neg_of_mem_skewPart
-- name    : GroundTheory.Automorphic.traceForm_neg_of_mem_skewPart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:25.771733+00:00
-- url     : https://prove2.me/theorems/a4551ca7-7993-4480-baeb-8adbf35f5395
-- title:
--   Automorphic: trace Form neg of mem skew Part
-- statement:
--   The Automorphic construction uses the trace Form neg of mem skew Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L144-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L144-L151

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
variable {L}

theorem GroundTheory.Automorphic.traceForm_neg_of_mem_skewPart {X : L} (hX : X ∈ skewPart L) (h0 : X ≠ 0) :
    traceForm L X X < 0 := by sorry
