-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_existsUnique_pow_mul_eq_comap
-- name    : FunctorialResolution.EmbeddedResolution.existsUnique_pow_mul_eq_comap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:00.458832+00:00
-- url     : https://prove2.me/theorems/a286feba-49b9-4cb2-beb3-e4f2c25cc889
-- title:
--   Embedded Resolution: exists Unique pow mul eq comap
-- statement:
--   The Embedded Resolution construction uses the exists Unique pow mul eq comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L472-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean#L472-L476

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

theorem FunctorialResolution.EmbeddedResolution.existsUnique_pow_mul_eq_comap [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z I : X.IdealSheafData) (n : ℕ) (hZ : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z))
    (hI : I ≤ Z ^ n) :
    ∃! J : X₁.IdealSheafData, Blowup.exceptionalIdeal π Z ^ n * J = I.comap π := by sorry
