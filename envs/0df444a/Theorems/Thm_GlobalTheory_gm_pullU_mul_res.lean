-- Prove2me | Theorems.Thm_GlobalTheory_gm_pullU_mul_res
-- name    : GlobalTheory.gm_pullU_mul_res
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:23.515851+00:00
-- url     : https://prove2.me/theorems/5cb48873-fc2b-4f56-a620-342dde583264
-- title:
--   Global Theory: gm pull U mul res
-- statement:
--   The Global Theory construction uses the gm pull U mul res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L54-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L54-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {Y : Scheme.{0}}

theorem GlobalTheory.gm_pullU_mul_res {X Z : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) {U : X.Opens} {W : Y.Opens}
    (le : F ⁻¹ᵁ U ≤ W) (hz : r z ∈ F ⁻¹ᵁ U) (G : Γ(X, U)ˣ) (t : Γ(Y, W)ˣ) :
    gm r z (F ⁻¹ᵁ U) (pullU F U G * res le t) = gm (r ≫ F) z U G * gm r z W t := by sorry
