-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_diagPow_eq
-- name    : GroundTheory.Automorphic.Parabolic.exists_diagPow_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:52.042811+00:00
-- url     : https://prove2.me/theorems/af371f2d-e147-4d32-92b4-c62609b7480c
-- title:
--   Parabolic: exists diag Pow eq
-- statement:
--   The Parabolic construction uses the exists diag Pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L28-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCharacters.lean#L28-L82

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCharacters
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {γ δ : Fin n → ℕ}

theorem GroundTheory.Automorphic.Parabolic.exists_diagPow_eq (h : ↥(levi F n γ ⊓ blockUpper F n δ)) :
    ∃ μ : Fin n → ℤ, ∀ {M : Type*} [CommMonoid M] (ψ : ↥(levi F n γ ⊓ blockUpper F n δ) →* M),
      (∀ k : ↥(levi F n γ ⊓ blockUpper F n δ), (k : GL (Fin n) F) ∈ integralGL F n → ψ k = 1) →
        ψ h = ψ ⟨Cartan.diagPow F n μ, diagPow_mem_levi_inf_blockUpper μ⟩ := by sorry
