-- Prove2me | Theorems.Thm_GlobalTheory_exists_isotropic_dual_of_skew
-- name    : GlobalTheory.exists_isotropic_dual_of_skew
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:12.060007+00:00
-- url     : https://prove2.me/theorems/0596e02d-e6e1-4c50-916c-6d9afaaed8a5
-- title:
--   Global Theory: exists isotropic dual of skew
-- statement:
--   The Global Theory construction uses the exists isotropic dual of skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsotropicDualOfSkewMatrix.lean#L6-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsotropicDualOfSkewMatrix.lean#L6-L29

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

theorem GlobalTheory.exists_isotropic_dual_of_skew {V : Type*} [AddCommGroup V] [Module ℚ V] {g : ℕ}
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (ε ψ : Fin g → V) (hB : ∀ x y, B x y = -B y x)
    (hε : ∀ i j, B (ε i) (ε j) = 0)
    (hψ : ∀ i j, B (ψ j) (ε i) = if i = j then 1 else 0) :
    ∃ φ : Fin g → V, (∀ i j, B (φ i) (φ j) = 0) ∧
      (∀ i j, B (φ j) (ε i) = if i = j then 1 else 0) ∧
      ∀ j, φ j - ψ j ∈ Submodule.span ℚ (Set.range ε) := by sorry
