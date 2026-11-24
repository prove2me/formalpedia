-- Prove2me | Theorems.Thm_GlobalTheory_Conv_halfCurve_inclusion
-- name    : GlobalTheory.Conv.halfCurve_inclusion
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:33.849538+00:00
-- url     : https://prove2.me/theorems/30c661d0-857b-4569-9f2a-6da0dd71bf05
-- title:
--   Conv: half Curve inclusion
-- statement:
--   The Conv construction uses the half Curve inclusion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L115-L120

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

theorem GlobalTheory.Conv.halfCurve_inclusion {T T' : ℝ} (h : T ≤ T') (yT : Sp (halfRing T) ⟶ Z) {w : ℂ}
    (hw : T' < w.im) :
    halfCurve (spMap (Subalgebra.inclusion (halfRing_mono h) : halfRing T →+* halfRing T') ≫ yT) w =
      halfCurve yT w := by sorry
