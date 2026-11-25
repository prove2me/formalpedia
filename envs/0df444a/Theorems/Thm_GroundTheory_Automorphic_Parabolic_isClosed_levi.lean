-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_levi
-- name    : GroundTheory.Automorphic.Parabolic.isClosed_levi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:30.500382+00:00
-- url     : https://prove2.me/theorems/b02d1919-8405-418a-b256-eb988130e434
-- title:
--   Parabolic: is Closed levi
-- statement:
--   The Parabolic construction uses the is Closed levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdmissibleInduction.lean#L77-L80

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

theorem GroundTheory.Automorphic.Parabolic.isClosed_levi : IsClosed (levi F n β : Set (GL (Fin n) F)) := by sorry
