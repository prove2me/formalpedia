-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_compl_sUnion_irreducibleComponents_sdiff_subset
-- name    : FunctorialResolution.EmbeddedResolution.compl_sUnion_irreducibleComponents_sdiff_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:15.56107+00:00
-- url     : https://prove2.me/theorems/49555035-a595-4de0-adde-dd9106449e2e
-- title:
--   Embedded Resolution: compl s Union irreducible Components sdiff subset
-- statement:
--   The Embedded Resolution construction uses the compl s Union irreducible Components sdiff subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L36-L45

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

theorem FunctorialResolution.EmbeddedResolution.compl_sUnion_irreducibleComponents_sdiff_subset (S : Set (Set α)) :
    (⋃₀ (irreducibleComponents α \ S))ᶜ ⊆ ⋃₀ S := by sorry
