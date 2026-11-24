-- Prove2me | Theorems.Thm_GlobalTheory_FinrankGrowthBounds_le_of_pow_le_mul_pow
-- name    : GlobalTheory.FinrankGrowthBounds.le_of_pow_le_mul_pow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:54.568978+00:00
-- url     : https://prove2.me/theorems/51a28f99-9b28-4290-8a0b-3898a51c5b8b
-- title:
--   Finrank Growth Bounds: le of pow le mul pow
-- statement:
--   The Finrank Growth Bounds construction uses the le of pow le mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L13-L22

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

theorem GlobalTheory.FinrankGrowthBounds.le_of_pow_le_mul_pow {a b C : ℕ} (hb : 1 ≤ b) (h : ∀ k : ℕ, a ^ k ≤ C * b ^ k) : a ≤ b := by sorry
