-- Prove2me | Theorems.Thm_GlobalTheory_gm_res_pullU
-- name    : GlobalTheory.gm_res_pullU
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:07:06.473598+00:00
-- url     : https://prove2.me/theorems/eed3974f-83fb-4e2f-b244-03ee6dbc111e
-- title:
--   Global Theory: gm res pull U
-- statement:
--   The Global Theory construction uses the gm res pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L49-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L49-L52

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

theorem GlobalTheory.gm_res_pullU {X Z : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) {U : X.Opens} {W : Y.Opens}
    (le : W ≤ F ⁻¹ᵁ U) (hz : r z ∈ W) (t : Γ(X, U)ˣ) :
    gm r z W (res le (pullU F U t)) = gm (r ≫ F) z U t := by sorry
