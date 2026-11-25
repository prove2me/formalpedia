-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_coe_leviParCoord_symm_single
-- name    : GroundTheory.Automorphic.Parabolic.coe_leviParCoord_symm_single
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:47.01615+00:00
-- url     : https://prove2.me/theorems/fdacade1-a253-514b-83f5-22b8e5b4bab5
-- title:
--   Parabolic: coe levi Par Coord symm single
-- statement:
--   The Parabolic construction uses the coe levi Par Coord symm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L227-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L227-L244

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}

theorem GroundTheory.Automorphic.Parabolic.coe_leviParCoord_symm_single (t : LeviParIndex n γ δ) :
    (((leviParCoord F n γ δ).symm (Pi.single t 1) : lieLeviPar F n γ δ) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 := by sorry
