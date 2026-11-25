-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_proper_flat_geometricallyIntegral_smooth
-- name    : GlobalTheory.WeierstrassCurve.proper_flat_geometricallyIntegral_smooth
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:21:56.673738+00:00
-- url     : https://prove2.me/theorems/60323512-48dd-5206-a5db-833ea6edf687
-- title:
--   Weierstrass Curve: proper flat geometrically Integral smooth
-- statement:
--   The Weierstrass Curve construction uses the proper flat geometrically Integral smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean#L419-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsStandardSmoothOfRelativeDimensionAwayJacobian.lean#L419-L426

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

theorem GlobalTheory.WeierstrassCurve.proper_flat_geometricallyIntegral_smooth :
    IsProper (toSpec W) ∧ Flat (toSpec W) ∧
      (LocallyOfFinitePresentation (toSpec W) ∧ QuasiCompact (toSpec W) ∧
        QuasiSeparated (toSpec W)) ∧
      GeometricallyIntegral (toSpec W) ∧
      (IsUnit W.Δ → SmoothOfRelativeDimension 1 (toSpec W)) := by sorry
