-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_traceForm_lie
-- name    : GroundTheory.Automorphic.traceForm_lie
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:03.03114+00:00
-- url     : https://prove2.me/theorems/cac1543b-e2f1-43d7-b574-3ee3d02988ac
-- title:
--   Automorphic: trace Form lie
-- statement:
--   The Automorphic construction uses the trace Form lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean#L34-L44

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

theorem GroundTheory.Automorphic.traceForm_lie (X Y Z : L) : traceForm L ⁅X, Y⁆ Z = -traceForm L Y ⁅X, Z⁆ := by sorry
