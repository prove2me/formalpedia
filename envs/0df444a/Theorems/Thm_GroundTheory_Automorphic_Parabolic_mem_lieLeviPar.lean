-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_lieLeviPar
-- name    : GroundTheory.Automorphic.Parabolic.mem_lieLeviPar
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:55:16.654331+00:00
-- url     : https://prove2.me/theorems/994f7f24-f585-4587-8bb0-7bc7edfe2b8e
-- title:
--   Parabolic: mem lie Levi Par
-- statement:
--   The Parabolic construction uses the mem lie Levi Par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L36-L38

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaModular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa MeasureTheory Measure Topology Set ValuativeRel Measures
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α α' : Type*} [LinearOrder α] [LinearOrder α'] (γ : Fin n → α) (δ : Fin n → α')
variable {F n γ δ}

theorem GroundTheory.Automorphic.Parabolic.mem_lieLeviPar {A : Matrix (Fin n) (Fin n) F} :
    A ∈ lieLeviPar F n γ δ ↔ ∀ i j, ¬ (γ i = γ j ∧ ¬ δ j < δ i) → A i j = 0 := by sorry
