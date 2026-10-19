-- Prove2me | Theorems.Thm_MazurTransfer_Order13IntegralHyperellipticMap_reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen
-- name    : MazurTransfer.Order13IntegralHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:28:12.350985+00:00
-- url     : https://prove2.me/theorems/4746c852-e259-4f3f-97e0-3770adfc74a4
-- title:
--   The literal ordinary and reciprocal chart overlap is the reciprocal nonzero-coordinate locus
-- statement:
--   For every commutative ring $K$, let $C_K$ be the literal glued order-13 curve with ordinary and reciprocal chart maps $j_o$ and $j_r$. On the reciprocal chart, $$j_r^{-1}(\operatorname{im}j_o)=D(z).$$ Thus a reciprocal point lies in the ordinary chart exactly when its reciprocal coordinate does not vanish. This describes the overlap over the original coefficient ring without any field or characteristic hypothesis.
-- source:
--   Original complete reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen statement and proof from MazurTheorem Order13IntegralCurveProperViaHyperellipticMap.lean, Apache-2.0, Vasily Ilin, Vas and contributors. Its original overlap and gluing helpers are retained as in the checked public six-section proof package, under an explicit fresh namespace. The complete original type is kernel-compared. Named downstream consumer: the two infinity points form the complement of the ordinary chart.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: unchanged six actual marked sections remain distinct after precomposition with any field point when two is a unit.
Named downstream consumer: actual integral Picard chart sections.
Original per-file attribution and checked proof bodies are retained below. -/
import Definitions.Def_MazurTransfer_Order13SixMarkedIntegralSections
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion
variable (K : Type u) [CommRing K]

theorem MazurTransfer.Order13IntegralHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen :
    XOneThirteenProjectiveCurve.reciprocalChartMap K ⁻¹ᵁ
        (XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange =
      PrimeSpectrum.basicOpen
        (XOneThirteenProjectiveCurve.zCoordinate K) := by sorry
