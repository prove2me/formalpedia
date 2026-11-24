-- Prove2me | Theorems.Thm_GlobalTheory_Conv_isHolTo_halfCurve
-- name    : GlobalTheory.Conv.isHolTo_halfCurve
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:27.4918+00:00
-- url     : https://prove2.me/theorems/8643ba90-4296-4223-b82b-e185e3a45767
-- title:
--   Conv: is Hol To half Curve
-- statement:
--   The Conv construction uses the is Hol To half Curve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L128-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L128-L138

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

theorem GlobalTheory.Conv.isHolTo_halfCurve {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) :
    IsHolTo {w : ℂ | T < w.im} (halfCurve yT) := by sorry
