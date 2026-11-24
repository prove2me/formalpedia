-- Prove2me | Theorems.Thm_GlobalTheory_lattice_eq_ideal_sum_and_mul_eq
-- name    : GlobalTheory.lattice_eq_ideal_sum_and_mul_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:10.811173+00:00
-- url     : https://prove2.me/theorems/6c951b48-dfa3-4e44-8ce2-bca6c2235908
-- title:
--   Global Theory: lattice eq ideal sum and mul eq
-- statement:
--   The Global Theory construction uses the lattice eq ideal sum and mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeFormIdealPairOfVectors.lean#L25-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LatticeFormIdealPairOfVectors.lean#L25-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LatticeFormIdealPairOfVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.lattice_eq_ideal_sum_and_mul_eq :
    ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v w : V}, v ≠ 0 → ∀ (I K : FractionalIdeal (𝓞 F)⁰ F), (∀ a : F, a ∈ I ↔ a • v ∈ L) →
    (∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) → B w v = 1 → (∀ t ∈ K, t • w ∈ L) →
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J := by sorry
