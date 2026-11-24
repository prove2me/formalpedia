-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv_transvection
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_transvection
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:23.184962+00:00
-- url     : https://prove2.me/theorems/101bdb2e-c5dc-463e-aa2f-d3f509f8fb25
-- title:
--   Measures: distrib Haar Char gl Equiv transvection
-- statement:
--   The Measures construction uses the distrib Haar Char gl Equiv transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L218-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L218-L276

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_transvection (t : Matrix.TransvectionStruct ι F)
    (h : t.toMatrix.det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) = 1 := by sorry
