-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_compl_sUnion_irreducibleComponents_sdiff
-- name    : FunctorialResolution.EmbeddedResolution.closure_compl_sUnion_irreducibleComponents_sdiff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:27.546315+00:00
-- url     : https://prove2.me/theorems/38efd856-af3c-4244-9237-0ad50cbad56e
-- title:
--   Embedded Resolution: closure compl s Union irreducible Components sdiff
-- statement:
--   The Embedded Resolution construction uses the closure compl s Union irreducible Components sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L47-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L47-L74

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

theorem FunctorialResolution.EmbeddedResolution.closure_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    closure ((⋃₀ (irreducibleComponents α \ S))ᶜ) = ⋃₀ S := by sorry
