-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_comap_map_of_isClosedImmersion
-- name    : FunctorialResolution.Blowup.comap_map_of_isClosedImmersion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:18.633921+00:00
-- url     : https://prove2.me/theorems/98e1e162-3b46-48ef-9711-deb3e9fe599b
-- title:
--   Blowup: comap map of is Closed Immersion
-- statement:
--   The Blowup construction uses the comap map of is Closed Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L81-L84

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open FunctorialResolution FunctorialResolution.Blowup

theorem FunctorialResolution.Blowup.comap_map_of_isClosedImmersion {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (Z.map ι).comap ι = Z := by sorry
