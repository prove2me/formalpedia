-- Prove2me | Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_add_right
-- name    : GlobalTheory.AppellHumbertTrivial.hermForm_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:53.107874+00:00
-- url     : https://prove2.me/theorems/c6086e9c-a40d-479c-88ee-c46598ca9444
-- title:
--   Appell Humbert Trivial: herm Form add right
-- statement:
--   The Appell Humbert Trivial construction uses the herm Form add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AppellHumbertTrivialOfNowhereVanishing.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AppellHumbertTrivialOfNowhereVanishing.lean#L50-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.AppellHumbertTrivial
variable {g : ℕ}
variable {g : ℕ}

theorem GlobalTheory.AppellHumbertTrivial.hermForm_add_right (B : Matrix (Fin g) (Fin g) ℂ) (x y w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w (x + y) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w x + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B w y := by sorry
