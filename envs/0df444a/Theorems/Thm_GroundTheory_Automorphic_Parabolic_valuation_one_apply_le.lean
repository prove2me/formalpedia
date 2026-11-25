-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_one_apply_le
-- name    : GroundTheory.Automorphic.Parabolic.valuation_one_apply_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:18:47.488052+00:00
-- url     : https://prove2.me/theorems/7141497c-0ce9-5d6d-b00f-52896bb48dac
-- title:
--   Parabolic: valuation one apply le
-- statement:
--   The Parabolic construction uses the valuation one apply le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L211-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L211-L216

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
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.valuation_one_apply_le (i j : Fin n) :
    valuation F ((1 : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := by sorry
