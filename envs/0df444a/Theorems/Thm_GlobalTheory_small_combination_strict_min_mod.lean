-- Prove2me | Theorems.Thm_GlobalTheory_small_combination_strict_min_mod
-- name    : GlobalTheory.small_combination_strict_min_mod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:28.334616+00:00
-- url     : https://prove2.me/theorems/b1d2e4f0-0a08-43c0-a3e6-29341aa653ae
-- title:
--   Global Theory: small combination strict min mod
-- statement:
--   The Global Theory construction uses the small combination strict min mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SmallCombinationStrictMinMod.lean#L77-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SmallCombinationStrictMinMod.lean#L77-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SmallCombinationStrictMinMod
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
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}

theorem GlobalTheory.small_combination_strict_min_mod :
    ∀ (X : Type) [AddCommGroup X] (Bf : X →+ X →+ ℤ) (Q : X → ℤ), (∀ x y, Bf x y = Bf y x) →
    (∀ x, 2 * Q x = Bf x x) → (∀ x, x ≠ 0 → 1 ≤ Q x) →
    ∀ (n D q : ℕ) (b : Fin n → X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) →
    (∀ j z, |(Bf (b j) z : ℝ)| ≤ M₀ * Q z) → (D : ℝ) * M₀ < q →
    ∀ e : Fin n → ℕ, ∑ j, e j ≤ D →
    ((Q (∑ j, e j • b j) : ℝ) ≤ (D : ℝ) ^ 2 * Cc) ∧
      ∀ z, z ≠ 0 → Q (∑ j, e j • b j) < Q (∑ j, e j • b j + q • z) := by sorry
