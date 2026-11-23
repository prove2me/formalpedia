-- Prove2me | Theorems.Thm_GlobalTheory_AppellHumbertTrivial_re_hermForm_add_self
-- name    : GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:16.731063+00:00
-- url     : https://prove2.me/theorems/55842c21-af50-4be3-a269-97c3b5e7bf3e
-- title:
--   Appell Humbert Trivial: re herm Form add self
-- statement:
--   The Appell Humbert Trivial construction uses the re herm Form add self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AppellHumbertTrivialOfNowhereVanishing.lean#L85-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AppellHumbertTrivialOfNowhereVanishing.lean#L85-L92

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

theorem GlobalTheory.AppellHumbertTrivial.re_hermForm_add_self {B : Matrix (Fin g) (Fin g) ℂ} (hB : B.IsHermitian)
    (x y : Fin g → ℂ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (x + y) (x + y)).re
      = (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x x).re + 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x y).re + (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B y y).re := by sorry
