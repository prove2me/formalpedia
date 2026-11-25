-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_rankTorus_conj_sub_le
-- name    : GroundTheory.Automorphic.Parabolic.valuation_rankTorus_conj_sub_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:55.425299+00:00
-- url     : https://prove2.me/theorems/874403d1-60a4-4b94-ade1-71fe0b9e06a3
-- title:
--   Parabolic: valuation rank Torus conj sub le
-- statement:
--   The Parabolic construction uses the valuation rank Torus conj sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L401-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L401-L419

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

theorem GroundTheory.Automorphic.Parabolic.valuation_rankTorus_conj_sub_le {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n β) (i j : Fin n) :
    valuation F ((rankTorus F n β e * u * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ϖ ^ e * valuation F (u i j - (1 : Matrix (Fin n) (Fin n) F) i j) := by sorry
