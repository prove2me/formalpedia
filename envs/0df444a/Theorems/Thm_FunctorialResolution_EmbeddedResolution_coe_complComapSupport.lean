-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complComapSupport
-- name    : FunctorialResolution.EmbeddedResolution.coe_complComapSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:31.085985+00:00
-- url     : https://prove2.me/theorems/90a818f9-2a0c-4ac3-88e8-c57ff5048cae
-- title:
--   Embedded Resolution: coe compl Comap Support
-- statement:
--   The Embedded Resolution construction uses the coe compl Comap Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IteratedBlowups/StrictTransformOffCenter.lean#L18-L19

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_StrictTransformOffCenter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.coe_complComapSupport {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData) :
    ((complComapSupport π Z : X₁.Opens) : Set X₁) = ((Z.comap π).support : Set X₁)ᶜ := by sorry
