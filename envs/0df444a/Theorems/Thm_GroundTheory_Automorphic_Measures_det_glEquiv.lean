-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_det_glEquiv
-- name    : GroundTheory.Automorphic.Measures.det_glEquiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:40.732022+00:00
-- url     : https://prove2.me/theorems/7bc0ebfc-8567-4209-a700-3f688dd91104
-- title:
--   Measures: det gl Equiv
-- statement:
--   The Measures construction uses the det gl Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L154-L160

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {F} {ι : Type*} [Fintype ι]
variable [DecidableEq ι]

theorem GroundTheory.Automorphic.Measures.det_glEquiv (g : GL ι F) :
    LinearEquiv.det (glEquiv g) = Matrix.GeneralLinearGroup.det g := by sorry
