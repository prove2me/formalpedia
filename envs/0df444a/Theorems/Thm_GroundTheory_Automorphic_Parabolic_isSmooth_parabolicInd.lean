-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_parabolicInd
-- name    : GroundTheory.Automorphic.Parabolic.isSmooth_parabolicInd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:10:46.466796+00:00
-- url     : https://prove2.me/theorems/48be5c7d-8dca-5984-879b-8cc681e95671
-- title:
--   Parabolic: is Smooth parabolic Ind
-- statement:
--   The Parabolic construction uses the is Smooth parabolic Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean#L106-L108

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
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
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem GroundTheory.Automorphic.Parabolic.isSmooth_parabolicInd (σ : Representation ℂ (levi F n β) W) :
    IsSmooth (parabolicInd F n β σ) := by sorry
