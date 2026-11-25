-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompact
-- name    : GroundTheory.Automorphic.Parabolic.mem_unipotentCompact
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:36.861226+00:00
-- url     : https://prove2.me/theorems/3d5b28a7-7fb7-46e9-8de5-373541a8a9db
-- title:
--   Parabolic: mem unipotent Compact
-- statement:
--   The Parabolic construction uses the mem unipotent Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L113-L117

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

theorem GroundTheory.Automorphic.Parabolic.mem_unipotentCompact {e : ℕ} {u : unipotentRadical F n β} :
    u ∈ unipotentCompact F n β e ↔
      rankTorus F n β e * u * (rankTorus F n β e)⁻¹ ∈ integralGL F n := by sorry
