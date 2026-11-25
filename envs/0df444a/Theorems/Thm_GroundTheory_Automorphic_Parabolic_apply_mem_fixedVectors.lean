-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_apply_mem_fixedVectors
-- name    : GroundTheory.Automorphic.Parabolic.apply_mem_fixedVectors
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:20:34.856346+00:00
-- url     : https://prove2.me/theorems/b6c502ae-9731-5439-91aa-54212619c162
-- title:
--   Parabolic: apply mem fixed Vectors
-- statement:
--   The Parabolic construction uses the apply mem fixed Vectors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L104-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L104-L122

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

theorem GroundTheory.Automorphic.Parabolic.apply_mem_fixedVectors {m : ℕ}
    (f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) :
    ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) k ∈
      fixedVectors σ ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by sorry
