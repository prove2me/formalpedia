-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permuteGL_mem_blockUpper_iff
-- name    : GroundTheory.Automorphic.Parabolic.permuteGL_mem_blockUpper_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:21:09.839641+00:00
-- url     : https://prove2.me/theorems/cef31c38-f3ff-5f6e-b3cf-6b44eb3e2456
-- title:
--   Parabolic: permute GL mem block Upper iff
-- statement:
--   The Parabolic construction uses the permute GL mem block Upper iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L54-L63

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
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
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem GroundTheory.Automorphic.Parabolic.permuteGL_mem_blockUpper_iff (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permuteGL F s g ∈ blockUpper F n β ↔ g ∈ blockUpper F n (β ∘ s) := by sorry
