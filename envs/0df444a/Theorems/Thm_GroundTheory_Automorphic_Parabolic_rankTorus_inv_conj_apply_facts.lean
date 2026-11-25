-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_conj_apply_facts
-- name    : GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_apply_facts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:24.255158+00:00
-- url     : https://prove2.me/theorems/1d2b106b-4f53-58a3-a92b-250c23b45924
-- title:
--   Parabolic: rank Torus inv conj apply facts
-- statement:
--   The Parabolic construction uses the rank Torus inv conj apply facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L186-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L186-L211

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

theorem GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_apply_facts {k t m : ℕ} (hm : k + t ≤ m) {z : GL (Fin n) F}
    (hz : z ∈ oppositeUnipotentRadical F n β)
    (hb : ∀ i j, (GLnLocal.uniformizer F : F) ^ k * z i j ∈ 𝒪[F]) (i j : Fin n) :
    ((rankTorus F n β m)⁻¹ * z * rankTorus F n β m : GL (Fin n) F) i j ∈ 𝒪[F] ∧
      valuation F (((rankTorus F n β m)⁻¹ * z * rankTorus F n β m : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F (GLnLocal.uniformizer F : F) ^ t := by sorry
