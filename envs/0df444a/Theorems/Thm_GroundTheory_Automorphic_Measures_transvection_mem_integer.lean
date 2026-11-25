-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_transvection_mem_integer
-- name    : GroundTheory.Automorphic.Measures.transvection_mem_integer
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:54.513163+00:00
-- url     : https://prove2.me/theorems/ffcc9164-0faf-410a-b30e-672902401974
-- title:
--   Measures: transvection mem integer
-- statement:
--   The Measures construction uses the transvection mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L171-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L171-L180

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

theorem GroundTheory.Automorphic.Measures.transvection_mem_integer {i j : ι} {c : F} (hc : c ∈ 𝒪[F]) (a b : ι) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by sorry
