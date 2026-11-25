-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_mem_blockUpper_dual
-- name    : GroundTheory.Automorphic.Parabolic.elimGL_mem_blockUpper_dual
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:19:32.872147+00:00
-- url     : https://prove2.me/theorems/b1520696-6d11-4ccb-9478-77500b8ecf39
-- title:
--   Parabolic: elim GL mem block Upper dual
-- statement:
--   The Parabolic construction uses the elim GL mem block Upper dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L100-L108

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
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}

theorem GroundTheory.Automorphic.Parabolic.elimGL_mem_blockUpper_dual (h : Matrix (Fin n) (Fin n) F) (a : Fin n) :
    elimGL β h a ∈ blockUpper F n (OrderDual.toDual ∘ β) := by sorry
