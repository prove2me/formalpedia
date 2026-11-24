-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafColon_ideal
-- name    : FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:46.661166+00:00
-- url     : https://prove2.me/theorems/8c647fa8-f082-4891-8de3-014c957d2cb5
-- title:
--   Embedded Resolution: ideal Sheaf Colon ideal
-- statement:
--   The Embedded Resolution construction uses the ideal Sheaf Colon ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L343-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L343-L346

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

theorem FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal [IsLocallyNoetherian Y] (I' F : Y.IdealSheafData)
    (U : Y.affineOpens) :
    (idealSheafColon I' F).ideal U = (I'.ideal U).colon (F.ideal U) := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.idealSheafColon_ideal
