-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_mem_hermPart
-- name    : GroundTheory.Automorphic.mem_hermPart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:25:09.414825+00:00
-- url     : https://prove2.me/theorems/fe7961e5-c2e2-4964-be8e-b46a7643fa89
-- title:
--   Automorphic: mem herm Part
-- statement:
--   The Automorphic construction uses the mem herm Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L109-L110

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

theorem GroundTheory.Automorphic.mem_hermPart {X : L} : X ∈ hermPart L ↔ (X : Matrix ι ι 𝕜)ᴴ = (X : Matrix ι ι 𝕜) := by sorry
