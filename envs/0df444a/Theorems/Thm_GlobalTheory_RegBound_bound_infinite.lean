-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_bound_infinite
-- name    : GlobalTheory.RegBound.bound_infinite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:18.435026+00:00
-- url     : https://prove2.me/theorems/411575df-0c80-4dca-8ec1-1c0bc799fa9f
-- title:
--   Reg Bound: bound infinite
-- statement:
--   The Reg Bound construction uses the bound infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L301-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L301-L396

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
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]

theorem GlobalTheory.RegBound.bound_infinite (σ : Type) [Finite σ] (k : ℕ) : ∀ q : ℕ → ℚ, ∃ d : ℕ,
    ∀ (K : Type) [Field K] [Infinite K] (I : Ideal (MvPolynomial σ K)),
      (∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) → (∀ F, (∀ i, X i * F ∈ I) → F ∈ I) →
      nmon σ 1 ≤ finrank K (piece I 1) + k →
      (∀ᶠ e in atTop, (finrank K (piece I e) : ℚ) = q e) →
      ∀ e ≥ d, (finrank K (piece I e) : ℚ) = q e ∧
        ∀ F ∈ I, F.IsHomogeneous (e + 1) → F ∈ genIn I e := by sorry
