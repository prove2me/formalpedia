-- Prove2me | Theorems.Thm_GlobalTheory_AppellHumbertTrivial_hermForm_smul_left
-- name    : GlobalTheory.AppellHumbertTrivial.hermForm_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:00.764807+00:00
-- url     : https://prove2.me/theorems/bb8eec92-3748-4a05-b67e-04b928b608bb
-- title:
--   Appell Humbert Trivial: herm Form smul left
-- statement:
--   The Appell Humbert Trivial construction uses the herm Form smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AppellHumbertTrivialOfNowhereVanishing.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/AppellHumbertTrivialOfNowhereVanishing.lean#L56-L59

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

theorem GlobalTheory.AppellHumbertTrivial.hermForm_smul_left (B : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B (t • x) w = t * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm B x w := by sorry
