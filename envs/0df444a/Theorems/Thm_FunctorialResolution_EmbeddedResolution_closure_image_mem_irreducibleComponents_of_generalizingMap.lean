-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_image_mem_irreducibleComponents_of_generalizingMap
-- name    : FunctorialResolution.EmbeddedResolution.closure_image_mem_irreducibleComponents_of_generalizingMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:37.465468+00:00
-- url     : https://prove2.me/theorems/31f23b9d-e579-4e6c-8ae0-8ef05f35da28
-- title:
--   Embedded Resolution: closure image mem irreducible Components of generalizing Map
-- statement:
--   The Embedded Resolution construction uses the closure image mem irreducible Components of generalizing Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SupportFlatPullback.lean#L15-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/SupportFlatPullback.lean#L15-L66

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_SupportFlatPullback
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

theorem FunctorialResolution.EmbeddedResolution.closure_image_mem_irreducibleComponents_of_generalizingMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : GeneralizingMap (fun x : ↥X => f x))
    {C : Set ↥X} (hC : C ∈ irreducibleComponents ↥X) :
    closure ((fun x : ↥X => f x) '' C) ∈ irreducibleComponents ↥Y := by sorry
