-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_parabolicChart_leftModulus_of_mem
-- name    : GroundTheory.Automorphic.GodementJacquet.parabolicChart_leftModulus_of_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:19.879735+00:00
-- url     : https://prove2.me/theorems/7f8c0950-275e-5944-83b8-fe29ac89a136
-- title:
--   Godement Jacquet: parabolic Chart left Modulus of mem
-- statement:
--   The Godement Jacquet construction uses the parabolic Chart left Modulus of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L406-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L406-L420

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJParabolicFubini
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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa Measures MeasureTheory Measure Topology Set
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]
variable {β : Fin n → α}

theorem GroundTheory.Automorphic.GodementJacquet.parabolicChart_leftModulus_of_mem {p : blockUpper F n β}
    (hp : (p : GL (Fin n) F) ∈ unipotentRadical F n β) :
    (parabolicChart F n β).leftModulus p = 1 := by sorry
