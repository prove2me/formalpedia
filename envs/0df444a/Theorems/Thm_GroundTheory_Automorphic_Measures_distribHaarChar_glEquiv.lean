-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:12:47.008561+00:00
-- url     : https://prove2.me/theorems/a26b9c3e-e4ac-4114-b3e4-1ccff980d7eb
-- title:
--   Measures: distrib Haar Char gl Equiv
-- statement:
--   The Measures construction uses the distrib Haar Char gl Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L278-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L278-L310

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv (g : GL ι F) :
    distribHaarChar (ι → F) (glEquiv g) = distribHaarChar F (Matrix.GeneralLinearGroup.det g) := by sorry
