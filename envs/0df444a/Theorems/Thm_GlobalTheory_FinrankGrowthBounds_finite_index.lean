-- Prove2me | Theorems.Thm_GlobalTheory_FinrankGrowthBounds_finite_index
-- name    : GlobalTheory.FinrankGrowthBounds.finite_index
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:31.482859+00:00
-- url     : https://prove2.me/theorems/7bee8003-3d19-4e2c-8e7b-3f03955b1137
-- title:
--   Finrank Growth Bounds: finite index
-- statement:
--   The Finrank Growth Bounds construction uses the finite index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L125-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L125-L138

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

theorem GlobalTheory.FinrankGrowthBounds.finite_index {R : Type*} [Field R] {M I : Type*} [AddCommGroup M] [Module R M]
    [Nontrivial M] [Module.Finite R (I → M)] : Finite I := by sorry
