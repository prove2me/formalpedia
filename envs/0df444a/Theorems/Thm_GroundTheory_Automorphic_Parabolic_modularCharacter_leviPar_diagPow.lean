-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_modularCharacter_leviPar_diagPow
-- name    : GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_diagPow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:14.443218+00:00
-- url     : https://prove2.me/theorems/89a4fab0-0bd2-513c-8f28-7ac29b09c131
-- title:
--   Parabolic: modular Character levi Par diag Pow
-- statement:
--   The Parabolic construction uses the modular Character levi Par diag Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L377-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaModular.lean#L377-L385

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α α' : Type*} [LinearOrder α] [LinearOrder α'] {γ : Fin n → α} {δ : Fin n → α'}

theorem GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_diagPow (μ : Fin n → ℤ) :
    modularCharacter (⟨Cartan.diagPow F n μ, diagPow_mem_leviPar μ⟩ : leviPar F n γ δ) =
      ∏ s : {ij : Fin n × Fin n // γ ij.1 = γ ij.2 ∧ δ ij.1 < δ ij.2},
        modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.1) /
          modulus ((GLnLocal.uniformizer F : F) ^ μ s.1.2) := by sorry
