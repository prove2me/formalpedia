-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_parabolicChart_leftModulus_parabolicMk
-- name    : GroundTheory.Automorphic.GodementJacquet.parabolicChart_leftModulus_parabolicMk
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:38:53.188501+00:00
-- url     : https://prove2.me/theorems/54cd556b-82d5-525c-949e-1f9d351f362a
-- title:
--   Godement Jacquet: parabolic Chart left Modulus parabolic Mk
-- statement:
--   The Godement Jacquet construction uses the parabolic Chart left Modulus parabolic Mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L422-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJParabolicFubini.lean#L422-L428

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

theorem GroundTheory.Automorphic.GodementJacquet.parabolicChart_leftModulus_parabolicMk (m : levi F n β) (u : UnipotentIndex n β → F) :
    (parabolicChart F n β).leftModulus (parabolicMk β m u) =
      (parabolicChart F n β).leftModulus (leviIncl m) := by sorry
