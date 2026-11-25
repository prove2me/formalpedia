-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isAdmissible_parabolicInd
-- name    : GroundTheory.Automorphic.Parabolic.isAdmissible_parabolicInd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:22:34.467871+00:00
-- url     : https://prove2.me/theorems/eabb30a0-842a-4f2e-97a3-a1c62ac6e848
-- title:
--   Parabolic: is Admissible parabolic Ind
-- statement:
--   The Parabolic construction uses the is Admissible parabolic Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L153-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L153-L191

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

theorem GroundTheory.Automorphic.Parabolic.isAdmissible_parabolicInd (hσ : IsAdmissible σ) : IsAdmissible (parabolicInd F n β σ) := by sorry
