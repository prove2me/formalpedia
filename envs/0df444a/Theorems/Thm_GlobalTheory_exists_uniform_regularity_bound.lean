-- Prove2me | Theorems.Thm_GlobalTheory_exists_uniform_regularity_bound
-- name    : GlobalTheory.exists_uniform_regularity_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:38.754428+00:00
-- url     : https://prove2.me/theorems/46b12dd3-061b-5d45-b7c7-2856dd8a6cf5
-- title:
--   Global Theory: exists uniform regularity bound
-- statement:
--   The Global Theory construction uses the exists uniform regularity bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L552-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L552-L574

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory
open RegBound

theorem GlobalTheory.exists_uniform_regularity_bound :
    ∀ (σ : Type) [Finite σ] (Q : Polynomial ℚ), ∃ d₀ : ℕ, ∀ (K : Type) [Field K] (I : Ideal (MvPolynomial σ K)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ F, (∀ i, MvPolynomial.X i * F ∈ I) → F ∈ I) → (∀ᶠ e in Filter.atTop, (Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) : ℚ) = Q.eval (e : ℚ)) → ∀ e ≥ d₀, (Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀} := by sorry
