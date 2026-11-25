-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviParChart_leftModulus
-- name    : GroundTheory.Automorphic.Parabolic.leviParChart_leftModulus
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:47:39.998815+00:00
-- url     : https://prove2.me/theorems/e0e59229-18c9-5c8c-89f7-bbb9bc969d7c
-- title:
--   Parabolic: levi Par Chart left Modulus
-- statement:
--   The Parabolic construction uses the levi Par Chart left Modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L178-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L178-L183

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
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
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')
variable {F n γ δ}
variable (F n γ δ)
variable {F n γ δ}

theorem GroundTheory.Automorphic.Parabolic.leviParChart_leftModulus (l : leviPar F n γ δ) :
    (leviParChart F n γ δ).leftModulus l =
      distribHaarChar F (LinearEquiv.det (mulLeftLeviPar F n γ δ l)) := by sorry
