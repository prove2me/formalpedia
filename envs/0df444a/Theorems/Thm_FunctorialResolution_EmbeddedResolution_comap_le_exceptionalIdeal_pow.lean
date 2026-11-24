-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_le_exceptionalIdeal_pow
-- name    : FunctorialResolution.EmbeddedResolution.comap_le_exceptionalIdeal_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:03.448796+00:00
-- url     : https://prove2.me/theorems/548a33fb-f7cf-47ae-80e3-54d4318e894e
-- title:
--   Embedded Resolution: comap le exceptional Ideal pow
-- statement:
--   The Embedded Resolution construction uses the comap le exceptional Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L466-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L466-L470

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

theorem FunctorialResolution.EmbeddedResolution.comap_le_exceptionalIdeal_pow (π : X₁ ⟶ X) {Z I : X.IdealSheafData} {n : ℕ}
    (hI : I ≤ Z ^ n) : I.comap π ≤ Blowup.exceptionalIdeal π Z ^ n := by sorry
