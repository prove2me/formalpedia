-- Prove2me | Theorems.Thm_GlobalTheory_exists_isotropic_dual_of_skew_matrix
-- name    : GlobalTheory.exists_isotropic_dual_of_skew_matrix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:09.352978+00:00
-- url     : https://prove2.me/theorems/80220a24-3399-418f-9837-8ff0242e77d2
-- title:
--   Global Theory: exists isotropic dual of skew matrix
-- statement:
--   The Global Theory construction uses the exists isotropic dual of skew matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsotropicDualOfSkewMatrix.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsotropicDualOfSkewMatrix.lean#L31-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsotropicDualOfSkewMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.exists_isotropic_dual_of_skew_matrix (r g : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ)
    (ε ψ : Fin g → Fin r → ℚ) (hM : Mqᵀ = -Mq) (hε : ∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0)
    (hψ : ∀ i j, ψ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) :
    ∃ φ : Fin g → Fin r → ℚ, (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) ∧
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by sorry
