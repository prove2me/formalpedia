-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_locally_isStandardSmoothOfRelativeDimension_originRing
-- name    : GlobalTheory.WeierstrassCurve.locally_isStandardSmoothOfRelativeDimension_originRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:30.495868+00:00
-- url     : https://prove2.me/theorems/b017ec4d-ca6b-444e-86e9-ac87960be485
-- title:
--   Weierstrass Curve: locally is Standard Smooth Of Relative Dimension origin Ring
-- statement:
--   The Weierstrass Curve construction uses the locally is Standard Smooth Of Relative Dimension origin Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean#L285-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean#L285-L291

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

theorem GlobalTheory.WeierstrassCurve.locally_isStandardSmoothOfRelativeDimension_originRing [W.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (OriginRing W)) := by sorry
