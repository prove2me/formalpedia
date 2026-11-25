-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_rankTorus_inv_conj_sub_le
-- name    : GroundTheory.Automorphic.Parabolic.valuation_rankTorus_inv_conj_sub_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:50.747336+00:00
-- url     : https://prove2.me/theorems/e0b4b492-f5c8-4c30-a780-7ac632fa7ad4
-- title:
--   Parabolic: valuation rank Torus inv conj sub le
-- statement:
--   The Parabolic construction uses the valuation rank Torus inv conj sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L421-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L421-L439

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

theorem GroundTheory.Automorphic.Parabolic.valuation_rankTorus_inv_conj_sub_le {e : ℕ} {z : GL (Fin n) F}
    (hz : z ∈ oppositeUnipotentRadical F n β) (i j : Fin n) :
    valuation F (((rankTorus F n β e)⁻¹ * z * rankTorus F n β e : GL (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ϖ ^ e * valuation F (z i j - (1 : Matrix (Fin n) (Fin n) F) i j) := by sorry
