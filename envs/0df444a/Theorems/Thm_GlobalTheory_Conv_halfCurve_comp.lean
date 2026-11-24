-- Prove2me | Theorems.Thm_GlobalTheory_Conv_halfCurve_comp
-- name    : GlobalTheory.Conv.halfCurve_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:04.351869+00:00
-- url     : https://prove2.me/theorems/3bfd70f6-78e3-45b0-ba75-8430f4b67a68
-- title:
--   Conv: half Curve comp
-- statement:
--   The Conv construction uses the half Curve comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L110-L113

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

theorem GlobalTheory.Conv.halfCurve_comp {T : ℝ} {Z' : Scheme.{0}} (yT : Sp (halfRing T) ⟶ Z) (j : Z ⟶ Z') (w : ℂ) :
    halfCurve (yT ≫ j) w = halfCurve yT w ≫ j := by sorry
