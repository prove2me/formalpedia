-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_pi_eq
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:23.352942+00:00
-- url     : https://prove2.me/theorems/ad3e870f-94d7-4173-8ba6-64176ade7512
-- title:
--   Measures: distrib Haar Char pi eq
-- statement:
--   The Measures construction uses the distrib Haar Char pi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L312-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L312-L315

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_pi_eq (L : (ι → F) ≃ₗ[F] (ι → F)) :
    distribHaarChar (ι → F) L = distribHaarChar F (LinearEquiv.det L) := by sorry
