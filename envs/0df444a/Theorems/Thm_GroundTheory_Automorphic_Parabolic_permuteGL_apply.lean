-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permuteGL_apply
-- name    : GroundTheory.Automorphic.Parabolic.permuteGL_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:21.193892+00:00
-- url     : https://prove2.me/theorems/ab2c62ff-177f-4df8-aa1b-552b0001ff42
-- title:
--   Parabolic: permute GL apply
-- statement:
--   The Parabolic construction uses the permute GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L39-L40

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

theorem GroundTheory.Automorphic.Parabolic.permuteGL_apply (s : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (i j : Fin n) :
    permuteGL F s g i j = g (s.symm i) (s.symm j) := by sorry
