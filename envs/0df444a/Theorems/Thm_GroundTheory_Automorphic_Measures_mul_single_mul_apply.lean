-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Measures_mul_single_mul_apply
-- name    : GroundTheory.Automorphic.Measures.mul_single_mul_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:10.191527+00:00
-- url     : https://prove2.me/theorems/77b470f2-f0e0-5fb4-aae4-56785935a6ae
-- title:
--   Measures: mul single mul apply
-- statement:
--   The Measures construction uses the mul single mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L204-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/MeasuresParabolic.lean#L204-L206

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

theorem GroundTheory.Automorphic.Measures.mul_single_mul_apply (A B : Matrix (Fin n) (Fin n) F) (a b i j : Fin n) :
    (A * Matrix.single a b (1 : F) * B) i j = A i a * B b j := by sorry
