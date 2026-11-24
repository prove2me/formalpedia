-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_distribHaarChar_eq_one_of_image_box
-- name    : GroundTheory.Automorphic.Measures.distribHaarChar_eq_one_of_image_box
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:45.35282+00:00
-- url     : https://prove2.me/theorems/318d6a84-cfa6-4875-8a07-24cca4e98740
-- title:
--   Measures: distrib Haar Char eq one of image box
-- statement:
--   The Measures construction uses the distrib Haar Char eq one of image box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L96-L103

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

theorem GroundTheory.Automorphic.Measures.distribHaarChar_eq_one_of_image_box {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h : L '' box F ι = box F ι) : distribHaarChar (ι → F) L = 1 := by sorry
