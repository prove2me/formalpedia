-- Prove2me | Theorems.Thm_GlobalTheory_FinrankGrowthBounds_eq_pow_of_growth
-- name    : GlobalTheory.FinrankGrowthBounds.eq_pow_of_growth
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:42.379621+00:00
-- url     : https://prove2.me/theorems/216d5667-6a73-4822-8a97-05308ee7c096
-- title:
--   Finrank Growth Bounds: eq pow of growth
-- statement:
--   The Finrank Growth Bounds construction uses the eq pow of growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L40-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L40-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology

theorem GlobalTheory.FinrankGrowthBounds.eq_pow_of_growth (h : ℕ → ℕ) (g : ℕ) (G : ℕ → Prop) (hG : ∀ m, G m ∨ G (m + 1))
    (hG0 : ¬ G 0) (h1 : h 1 = 1)
    (hmono : Monotone h) (hrel : ∀ n j, G n → 1 ≤ j → h (n ^ 2 * j) = h (n ^ 2) * h j)
    (N c C : ℕ) (hN : 1 ≤ N)
    (hgr : ∀ t, 1 ≤ t → t ^ g ≤ c * h (N * t) ∧ h (N * t) ≤ C * t ^ g) (j : ℕ) (hj : 1 ≤ j) :
    h j = j ^ g := by sorry
