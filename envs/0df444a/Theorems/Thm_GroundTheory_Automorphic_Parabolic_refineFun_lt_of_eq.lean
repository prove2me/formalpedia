-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_refineFun_lt_of_eq
-- name    : GroundTheory.Automorphic.Parabolic.refineFun_lt_of_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:46:15.149795+00:00
-- url     : https://prove2.me/theorems/9d826d25-c2f4-5bb7-915b-0b997c4318bb
-- title:
--   Parabolic: refine Fun lt of eq
-- statement:
--   The Parabolic construction uses the refine Fun lt of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L362-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L362-L365

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

theorem GroundTheory.Automorphic.Parabolic.refineFun_lt_of_eq {β γ : Fin n → ℕ} {i j : Fin n} (hβ : β i = β j) :
    refineFun β γ j < refineFun β γ i ↔ γ j < γ i := by sorry
