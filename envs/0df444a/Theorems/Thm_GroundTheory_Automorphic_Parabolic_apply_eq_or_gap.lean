-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_eq_or_gap
-- name    : GroundTheory.Automorphic.Parabolic.apply_eq_or_gap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:43.443338+00:00
-- url     : https://prove2.me/theorems/300211e2-cbba-5634-8a6b-7274ca471ea2
-- title:
--   Parabolic: apply eq or gap
-- statement:
--   The Parabolic construction uses the apply eq or gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L226-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalAdmissible.lean#L226-L255

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

theorem GroundTheory.Automorphic.Parabolic.apply_eq_or_gap {θ C : ℤ} {b : α} {μ : Fin n → ℤ}
    (hgap : ∀ k, β k = b → μ k < θ → μ k + C ≤ θ) {u : GL (Fin n) F} (hu : u ∈ levi F n β)
    (hN : u ∈ unipotentRadical F n (splitFun (Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j)))
    (i j : Fin n) : u i j = (1 : Matrix (Fin n) (Fin n) F) i j ∨ μ j + C ≤ μ i := by sorry
