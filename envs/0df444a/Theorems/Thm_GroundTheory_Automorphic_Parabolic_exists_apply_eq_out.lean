-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_apply_eq_out
-- name    : GroundTheory.Automorphic.Parabolic.exists_apply_eq_out
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:05.393469+00:00
-- url     : https://prove2.me/theorems/dfbedfd7-b6a4-4dc4-b480-fd9106c124e4
-- title:
--   Parabolic: exists apply eq out
-- statement:
--   The Parabolic construction uses the exists apply eq out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L124-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L124-L151

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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem GroundTheory.Automorphic.Parabolic.exists_apply_eq_out (m : ℕ) (x : GL (Fin n) F) :
    ∃ (p : blockUpper F n β) (c : integralGL F n ⧸ (congruenceSubgroup F n m).subgroupOf
      (integralGL F n)), ∀ f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
      ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x =
        sqrtModular F n β p • σ (leviProj F n β p)
          (((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : integralGL F n) : GL (Fin n) F)) := by sorry
