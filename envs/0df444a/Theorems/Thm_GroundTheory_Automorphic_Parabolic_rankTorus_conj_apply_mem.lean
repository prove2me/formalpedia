-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_conj_apply_mem
-- name    : GroundTheory.Automorphic.Parabolic.rankTorus_conj_apply_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:35.556691+00:00
-- url     : https://prove2.me/theorems/965fab9f-ab03-439b-8851-767c16f44eb3
-- title:
--   Parabolic: rank Torus conj apply mem
-- statement:
--   The Parabolic construction uses the rank Torus conj apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L87-L105

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

theorem GroundTheory.Automorphic.Parabolic.rankTorus_conj_apply_mem {e : ℕ} {u : GL (Fin n) F} (hu : u ∈ unipotentRadical F n β)
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ e * u i j ∈ 𝒪[F]) (i j : Fin n) :
    (rankTorus F n β e * u * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] := by sorry
