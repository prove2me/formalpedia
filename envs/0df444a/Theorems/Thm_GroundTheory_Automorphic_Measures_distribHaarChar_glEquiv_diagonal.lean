-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_glEquiv_diagonal
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_diagonal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:20.076076+00:00
-- url     : https://prove2.me/theorems/30289c90-b678-4dfa-b604-ff3cd45316aa
-- title:
--   Measures: distrib Haar Char gl Equiv diagonal
-- statement:
--   The Measures construction uses the distrib Haar Char gl Equiv diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L182-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L182-L216

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_glEquiv_diagonal {D : ι → F} (h : (Matrix.diagonal D).det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) =
      distribHaarChar F (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) := by sorry
