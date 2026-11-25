-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_finset_of_isCuspidal
-- name    : GroundTheory.Automorphic.Parabolic.exists_finset_of_isCuspidal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:39:56.847022+00:00
-- url     : https://prove2.me/theorems/31224d25-ba4b-4196-9aed-62b158f27dcf
-- title:
--   Parabolic: exists finset of is Cuspidal
-- statement:
--   The Parabolic construction uses the exists finset of is Cuspidal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L201-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L201-L224

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
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
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.exists_finset_of_isCuspidal {σ : Representation ℂ (levi F n β) W} (hc : IsCuspidal σ)
    {S : Finset (Fin n)} (hS : ∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S) (w : W) :
    ∃ U : Finset (levi F n β), (∀ u ∈ U, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun S)) ∧
      w ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ x, y = σ u x - x} := by sorry
