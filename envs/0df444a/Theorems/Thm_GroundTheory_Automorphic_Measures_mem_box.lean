-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mem_box
-- name    : GroundTheory.Automorphic.Measures.mem_box
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:53.14548+00:00
-- url     : https://prove2.me/theorems/54e21fb6-ee3e-4659-8e52-005372dfe1e7
-- title:
--   Measures: mem box
-- statement:
--   The Measures construction uses the mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresModulus.lean#L85-L86

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

theorem GroundTheory.Automorphic.Measures.mem_box {x : ι → F} : x ∈ box F ι ↔ ∀ i, x i ∈ 𝒪[F] := by sorry
