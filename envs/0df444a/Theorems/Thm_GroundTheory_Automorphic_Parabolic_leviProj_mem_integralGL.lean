-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_mem_integralGL
-- name    : GroundTheory.Automorphic.Parabolic.leviProj_mem_integralGL
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:50:45.51413+00:00
-- url     : https://prove2.me/theorems/cfef8fb1-007c-4c98-b887-645faa9b1c89
-- title:
--   Parabolic: levi Proj mem integral GL
-- statement:
--   The Parabolic construction uses the levi Proj mem integral GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean#L151-L155

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_EntryBound_leviProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {α : Type*} [LinearOrder α] {β : Fin n → α}

theorem GroundTheory.Automorphic.Parabolic.leviProj_mem_integralGL {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) ∈ integralGL F n := by sorry
