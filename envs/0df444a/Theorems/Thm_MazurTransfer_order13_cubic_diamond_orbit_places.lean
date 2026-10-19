-- Prove2me | Theorems.Thm_MazurTransfer_order13_cubic_diamond_orbit_places
-- name    : MazurTransfer.order13_cubic_diamond_orbit_places
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T19:42:24.246993+00:00
-- url     : https://prove2.me/theorems/fa1ed5e8-177f-48a3-b5d0-1fd3977df78d
-- title:
--   The four inverse diamond orbit places are the ordinary cusp places
-- statement:
--   The four original inverse diamond orbit places of the two infinity places equal the named ordinary cusp places. This is the conjunction of four exact original closed equalities and supports the infinity divisor class eigenvalue.
-- source:
--   MazurTheorem Order13CubicPlaceOrderCharacterization and Order13CubicHyperellipticPlaceAction; four original closed equalities retained; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13CubicPrincipalDivisorAndCuspClassOriginalDataAndCertificatesExplicitPlaceSurjectivityV220261018
import Definitions.Def_MazurTransfer_Order13CubicDiamondOrbitOriginalDataAndCertificates20261018
noncomputable section
open MazurTransfer
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13CubicDiamondOrbitValuations Order13CubicActualCuspValuations
local instance publicCubicDiamondOrbitPlacesFactProvider20261018 : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.order13_cubic_diamond_orbit_places : firstPositivePlace = zeroPositivePlace ∧
      firstNegativePlace = zeroNegativePlace ∧
      secondPositivePlace = negOnePositivePlace ∧
      secondNegativePlace = negOneNegativePlace := by sorry
