-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_subgroupOf_levi
-- name    : GroundTheory.Automorphic.Parabolic.isOpen_subgroupOf_levi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:21:43.845478+00:00
-- url     : https://prove2.me/theorems/644a93a9-bbe3-4683-8196-072793e2885c
-- title:
--   Parabolic: is Open subgroup Of levi
-- statement:
--   The Parabolic construction uses the is Open subgroup Of levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L94-L98

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

theorem GroundTheory.Automorphic.Parabolic.isOpen_subgroupOf_levi {K : Subgroup (GL (Fin n) F)}
    (hK : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen ((K.subgroupOf (levi F n β) : Subgroup (levi F n β)) : Set (levi F n β)) := by sorry
