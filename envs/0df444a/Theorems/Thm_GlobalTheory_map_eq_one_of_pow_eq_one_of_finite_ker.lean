-- Prove2me | Theorems.Thm_GlobalTheory_map_eq_one_of_pow_eq_one_of_finite_ker
-- name    : GlobalTheory.map_eq_one_of_pow_eq_one_of_finite_ker
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:06.448136+00:00
-- url     : https://prove2.me/theorems/71503885-1fbd-4fc8-b4c8-fef22f11a4cc
-- title:
--   Global Theory: map eq one of pow eq one of finite ker
-- statement:
--   The Global Theory construction uses the map eq one of pow eq one of finite ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedTorusExtensionOfPowEqOne.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedTorusExtensionOfPowEqOne.lean#L12-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedTorusExtensionOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.map_eq_one_of_pow_eq_one_of_finite_ker {H B : Type*} [Group H] [Group B] (φ : H →* B)
    [Finite φ.ker] {n : ℕ} (hn : n.Prime) (h : ∀ x : H, x ^ n = 1 → x = 1) (y : H)
    (hy : φ y ^ n = 1) : φ y = 1 := by sorry
