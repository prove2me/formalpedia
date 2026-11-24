-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_eq_one_of_mapsTo_box
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_eq_one_of_mapsTo_box
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:54.671377+00:00
-- url     : https://prove2.me/theorems/1399d01c-0bbc-4e48-b898-72dbf32a7311
-- title:
--   Measures: distrib Haar Char eq one of maps To box
-- statement:
--   The Measures construction uses the distrib Haar Char eq one of maps To box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L105-L111

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_eq_one_of_mapsTo_box {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h₁ : ∀ x ∈ box F ι, L x ∈ box F ι) (h₂ : ∀ x ∈ box F ι, L.symm x ∈ box F ι) :
    distribHaarChar (ι → F) L = 1 := by sorry
