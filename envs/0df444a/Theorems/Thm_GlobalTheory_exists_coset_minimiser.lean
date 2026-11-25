-- Prove2me | Theorems.Thm_GlobalTheory_exists_coset_minimiser
-- name    : GlobalTheory.exists_coset_minimiser
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:09.959801+00:00
-- url     : https://prove2.me/theorems/bb144d2d-cf38-4b21-beb6-c3e41eb2fbbf
-- title:
--   Global Theory: exists coset minimiser
-- statement:
--   The Global Theory construction uses the exists coset minimiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L117-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsPosZsmulMemRange.lean#L117-L185

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory

theorem GlobalTheory.exists_coset_minimiser :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) → (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) → ∀ (n : ℕ) (b : Module.Basis (Fin n) ℤ X) (Cc : ℝ), (∀ j, (Q (b j) : ℝ) ≤ Cc) → ∀ (φ : X →+ X) (g : ℕ), 1 ≤ g → (∀ x y, Bf (φ x) (φ y) = g * Bf x y) → ∀ x : X, ∃ χ : X, ((Q (x + φ χ) : ℝ) ≤ g * n * Cc / 4) ∧ ∀ (q : ℕ) (z : X), (q : ℤ) * (q - 1) * Q (φ z) ≤ Q (x + φ χ + q • φ z) - Q (x + φ χ) := by sorry
