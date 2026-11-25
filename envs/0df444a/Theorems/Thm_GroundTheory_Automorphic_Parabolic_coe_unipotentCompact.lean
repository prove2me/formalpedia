-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_unipotentCompact
-- name    : GroundTheory.Automorphic.Parabolic.coe_unipotentCompact
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:16.971992+00:00
-- url     : https://prove2.me/theorems/2ccb42bf-d7d3-4fcd-91fb-9a005e41df41
-- title:
--   Parabolic: coe unipotent Compact
-- statement:
--   The Parabolic construction uses the coe unipotent Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L122-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.coe_unipotentCompact (e : ℕ) :
    (unipotentCompact F n β e : Set (unipotentRadical F n β)) =
      Subtype.val ⁻¹' (conjHomeomorph (rankTorus F n β e) ⁻¹' (integralGL F n : Set _)) := by sorry
