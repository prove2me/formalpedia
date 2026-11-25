-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_skewPart
-- name    : GroundTheory.Automorphic.mem_skewPart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:25:24.295141+00:00
-- url     : https://prove2.me/theorems/a4d2e35c-2961-4547-96b5-fabfcd826e68
-- title:
--   Automorphic: mem skew Part
-- statement:
--   The Automorphic construction uses the mem skew Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L106-L107

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

theorem GroundTheory.Automorphic.mem_skewPart {X : L} : X ∈ skewPart L ↔ (X : Matrix ι ι 𝕜)ᴴ = -(X : Matrix ι ι 𝕜) := by sorry
