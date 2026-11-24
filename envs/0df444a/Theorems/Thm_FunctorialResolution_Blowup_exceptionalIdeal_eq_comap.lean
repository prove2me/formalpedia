-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_exceptionalIdeal_eq_comap
-- name    : FunctorialResolution.Blowup.exceptionalIdeal_eq_comap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:42.84588+00:00
-- url     : https://prove2.me/theorems/f892e96e-23f6-4540-acb8-3a31710dbb42
-- title:
--   Blowup: exceptional Ideal eq comap
-- statement:
--   The Blowup construction uses the exceptional Ideal eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/StrictTransform.lean#L15-L16

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup
noncomputable section

theorem FunctorialResolution.Blowup.exceptionalIdeal_eq_comap {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    exceptionalIdeal f Z = Z.comap f := by sorry
