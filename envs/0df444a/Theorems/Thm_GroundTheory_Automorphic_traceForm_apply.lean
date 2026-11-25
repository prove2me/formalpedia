-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_traceForm_apply
-- name    : GroundTheory.Automorphic.traceForm_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:03.895108+00:00
-- url     : https://prove2.me/theorems/8e3d8217-485c-4bf2-b3af-3a76b1c76381
-- title:
--   Automorphic: trace Form apply
-- statement:
--   The Automorphic construction uses the trace Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L28-L29

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

theorem GroundTheory.Automorphic.traceForm_apply (X Y : L) :
    traceForm L X Y = RCLike.re (trace ((X : Matrix ι ι 𝕜) * (Y : Matrix ι ι 𝕜))) := by sorry
