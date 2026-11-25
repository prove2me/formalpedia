-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_refineFun_eq_iff
-- name    : GroundTheory.Automorphic.Parabolic.refineFun_eq_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:49.583908+00:00
-- url     : https://prove2.me/theorems/27ac0d57-94fa-4196-b166-5d579ef60434
-- title:
--   Parabolic: refine Fun eq iff
-- statement:
--   The Parabolic construction uses the refine Fun eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L347-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L347-L360

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem GroundTheory.Automorphic.Parabolic.refineFun_eq_iff {β γ : Fin n → ℕ} {i j : Fin n} :
    refineFun β γ i = refineFun β γ j ↔ β i = β j ∧ γ i = γ j := by sorry
