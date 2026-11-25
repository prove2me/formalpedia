-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_permuteGL_mem_integralGL_iff
-- name    : GroundTheory.Automorphic.Parabolic.permuteGL_mem_integralGL_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:21:22.280633+00:00
-- url     : https://prove2.me/theorems/07249074-e895-4365-a99b-059a2346b463
-- title:
--   Parabolic: permute GL mem integral GL iff
-- statement:
--   The Parabolic construction uses the permute GL mem integral GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L42-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L42-L52

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

theorem GroundTheory.Automorphic.Parabolic.permuteGL_mem_integralGL_iff (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permuteGL F s g ∈ integralGL F n ↔ g ∈ integralGL F n := by sorry
