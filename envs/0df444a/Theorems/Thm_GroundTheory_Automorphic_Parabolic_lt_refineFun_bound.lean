-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_lt_refineFun_bound
-- name    : GroundTheory.Automorphic.Parabolic.lt_refineFun_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:50:47.22316+00:00
-- url     : https://prove2.me/theorems/c3af3727-0095-487e-9a99-fde88573bd9a
-- title:
--   Parabolic: lt refine Fun bound
-- statement:
--   The Parabolic construction uses the lt refine Fun bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L336-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/JacquetAdmissible.lean#L336-L337

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

theorem GroundTheory.Automorphic.Parabolic.lt_refineFun_bound (γ : Fin n → ℕ) (i : Fin n) : γ i < Finset.univ.sup γ + 1 := by sorry
