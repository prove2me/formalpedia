-- Prove2me | Theorems.Thm_GlobalTheory_T_latticeCount_prod_of_idempotent_separable
-- name    : GlobalTheory.T.latticeCount_prod_of_idempotent_separable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:37.221789+00:00
-- url     : https://prove2.me/theorems/b3bbc4a5-0036-4268-9f4b-f2ac3bd91faf
-- title:
--   T: lattice Count prod of idempotent separable
-- statement:
--   The T construction uses the lattice Count prod of idempotent separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparableStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparableStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.latticeCount_prod_of_idempotent_separable : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ((1, 0) : B₁.A × B₂.A) ∈ Algebra.adjoin K.O ({(B₁.g, B₂.g)} : Set (B₁.A × B₂.A)) → (B₁.P * B₂.P).Separable → ∀ (x₁ : B₁.A) (x₂ : B₂.A), IsUnit x₁ → IsUnit x₂ → B₁.σ x₁ = x₁ → B₂.σ x₂ = x₂ → (B₁.prod B₂).N (x₁, x₂) = B₁.N x₁ * B₂.N x₂ := by sorry
