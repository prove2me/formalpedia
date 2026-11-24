-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mulVec_mem_box
-- name    : GroundTheory.Automorphic.Measures.mulVec_mem_box
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:23.785231+00:00
-- url     : https://prove2.me/theorems/d0324193-5608-4dbf-ad78-44ec7fd6a9c2
-- title:
--   Measures: mul Vec mem box
-- statement:
--   The Measures construction uses the mul Vec mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L115-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L115-L117

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

theorem GroundTheory.Automorphic.Measures.mulVec_mem_box {A : Matrix ι ι F} (hA : ∀ i j, A i j ∈ 𝒪[F]) {x : ι → F}
    (hx : x ∈ box F ι) : A.mulVec x ∈ box F ι := by sorry
