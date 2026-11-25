-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_inv_conj_mem_congruenceSubgroup
-- name    : GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_mem_congruenceSubgroup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:29.801224+00:00
-- url     : https://prove2.me/theorems/85b83de4-7b43-4790-be33-4889e7363c96
-- title:
--   Parabolic: rank Torus inv conj mem congruence Subgroup
-- statement:
--   The Parabolic construction uses the rank Torus inv conj mem congruence Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L461-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L461-L482

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
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
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_mem_congruenceSubgroup {e m : ℕ} {z : GL (Fin n) F}
    (hz : z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β) :
    (rankTorus F n β e)⁻¹ * z * rankTorus F n β e ∈
      congruenceSubgroup F n (m + e) ⊓ oppositeUnipotentRadical F n β := by sorry
