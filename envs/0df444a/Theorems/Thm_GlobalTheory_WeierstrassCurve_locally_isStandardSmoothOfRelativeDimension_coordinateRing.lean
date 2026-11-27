-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_locally_isStandardSmoothOfRelativeDimension_coordinateRing
-- name    : GlobalTheory.WeierstrassCurve.locally_isStandardSmoothOfRelativeDimension_coordinateRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:15.463262+00:00
-- url     : https://prove2.me/theorems/edfd3da4-ec6a-5020-a644-a0a71db4f1fa
-- title:
--   Weierstrass Curve: locally is Standard Smooth Of Relative Dimension coordinate Ring
-- statement:
--   The Weierstrass Curve construction uses the locally is Standard Smooth Of Relative Dimension coordinate Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean#L277-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean#L277-L283

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open MvPolynomial
variable {i j : Fin 3} (hij : j ≠ i)

theorem GlobalTheory.WeierstrassCurve.locally_isStandardSmoothOfRelativeDimension_coordinateRing [W.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R W.toAffine.CoordinateRing) := by sorry
