-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mul_mul_apply_mem_integer
-- name    : GroundTheory.Automorphic.Measures.mul_mul_apply_mem_integer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:56.17559+00:00
-- url     : https://prove2.me/theorems/971032db-1dce-5ee8-a253-fba478409c84
-- title:
--   Measures: mul mul apply mem integer
-- statement:
--   The Measures construction uses the mul mul apply mem integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L489-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L489-L495

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable (F n β)
variable {F n β}

theorem GroundTheory.Automorphic.Measures.mul_mul_apply_mem_integer {A M B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hM : ∀ i j, M i j ∈ 𝒪[F]) (hB : ∀ i j, B i j ∈ 𝒪[F]) (i j : Fin n) :
    (A * M * B) i j ∈ 𝒪[F] := by sorry
