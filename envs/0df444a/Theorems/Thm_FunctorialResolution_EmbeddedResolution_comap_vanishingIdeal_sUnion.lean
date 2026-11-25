-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_vanishingIdeal_sUnion
-- name    : FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_sUnion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:53:14.87109+00:00
-- url     : https://prove2.me/theorems/c4a25055-3854-4de2-b81f-4159c3af22fc
-- title:
--   Embedded Resolution: comap vanishing Ideal s Union
-- statement:
--   The Embedded Resolution construction uses the comap vanishing Ideal s Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L115-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/VanishingIdealOfComponents.lean#L115-L175

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

theorem FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_sUnion {X X' : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced X']
    [NoetherianSpace ↥X] [NoetherianSpace ↥X'] [AlgebraicGeometry.Flat f]
    {S : Set (Set ↥X)} (hS : S ⊆ irreducibleComponents ↥X)
    {Z : Closeds ↥X} (hZ : (Z : Set ↥X) = ⋃₀ S)
    {Z' : Closeds ↥X'} (hZ' : (Z' : Set ↥X') = f.base ⁻¹' (⋃₀ S)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' := by sorry
