-- Prove2me | Theorems.Thm_GlobalTheory_Conv_halfCurve_eq
-- name    : GlobalTheory.Conv.halfCurve_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:00.890418+00:00
-- url     : https://prove2.me/theorems/71448618-2859-4ac7-85bb-39d2708e1608
-- title:
--   Conv: half Curve eq
-- statement:
--   The Conv construction uses the half Curve eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L107-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}

theorem GlobalTheory.Conv.halfCurve_eq {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) {w : ℂ} (hw : T < w.im) :
    halfCurve yT w = spMap (ev T w hw : halfRing T →+* ℂ) ≫ yT := by sorry
