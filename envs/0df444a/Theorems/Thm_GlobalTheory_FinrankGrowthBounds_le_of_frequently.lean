-- Prove2me | Theorems.Thm_GlobalTheory_FinrankGrowthBounds_le_of_frequently
-- name    : GlobalTheory.FinrankGrowthBounds.le_of_frequently
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:48.612269+00:00
-- url     : https://prove2.me/theorems/3b2ee940-2ca1-432e-9641-598ca57437e5
-- title:
--   Finrank Growth Bounds: le of frequently
-- statement:
--   The Finrank Growth Bounds construction uses the le of frequently property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L24-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L24-L38

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

theorem GlobalTheory.FinrankGrowthBounds.le_of_frequently {a b g : ℕ} (h : ∀ M : ℕ, ∃ n, M ≤ n ∧ a * n ^ g ≤ b * (n + 8) ^ g) :
    a ≤ b := by sorry
