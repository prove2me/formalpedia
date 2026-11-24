-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_eq_controlledTransform_of_mul_eq_comap
-- name    : FunctorialResolution.EmbeddedResolution.eq_controlledTransform_of_mul_eq_comap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:40.688876+00:00
-- url     : https://prove2.me/theorems/33743065-0dbe-4383-89d5-3c6eab0f9f21
-- title:
--   Embedded Resolution: eq controlled Transform of mul eq comap
-- statement:
--   The Embedded Resolution construction uses the eq controlled Transform of mul eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L499-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L499-L504

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

theorem FunctorialResolution.EmbeddedResolution.eq_controlledTransform_of_mul_eq_comap [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hI : I ≤ Z ^ n)
    (J : X₁.IdealSheafData) (hJ : Blowup.exceptionalIdeal π Z ^ n * J = I.comap π) :
    J = controlledTransform π Z I n hπ hI := by sorry
