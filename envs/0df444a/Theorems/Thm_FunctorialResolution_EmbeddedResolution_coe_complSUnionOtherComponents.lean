-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_coe_complSUnionOtherComponents
-- name    : FunctorialResolution.EmbeddedResolution.coe_complSUnionOtherComponents
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:45.496803+00:00
-- url     : https://prove2.me/theorems/566d0e2c-a06b-440e-a31d-2df9633eddd9
-- title:
--   Embedded Resolution: coe compl SUnion Other Components
-- statement:
--   The Embedded Resolution construction uses the coe compl SUnion Other Components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L87-L89

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_VanishingIdealOfComponents
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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {α : Type*} [TopologicalSpace α]

theorem FunctorialResolution.EmbeddedResolution.coe_complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.coe_complSUnionOtherComponents
