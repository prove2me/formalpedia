-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exceptionalIdeal_pow_mul_controlledTransform
-- name    : FunctorialResolution.EmbeddedResolution.exceptionalIdeal_pow_mul_controlledTransform
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:15.29288+00:00
-- url     : https://prove2.me/theorems/936cbde0-8741-48f2-9094-e3b6ecfbe199
-- title:
--   Embedded Resolution: exceptional Ideal pow mul controlled Transform
-- statement:
--   The Embedded Resolution construction uses the exceptional Ideal pow mul controlled Transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L490-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L490-L497

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
variable {X X₁ : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.exceptionalIdeal_pow_mul_controlledTransform [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n) :
    Blowup.exceptionalIdeal π Z ^ n * controlledTransform π Z I n hπ hI = I.comap π := by sorry
