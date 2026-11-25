-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_modularCharacter_leviPar
-- name    : GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:32.031399+00:00
-- url     : https://prove2.me/theorems/572c638e-a6aa-48cd-bc1a-edd05774409e
-- title:
--   Parabolic: modular Character levi Par
-- statement:
--   The Parabolic construction uses the modular Character levi Par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L200-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L200-L206

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

theorem GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar (l : leviPar F n γ δ) :
    modularCharacter l = distribHaarChar F (LinearEquiv.det (adLeviPar F n γ δ l)) := by sorry
