-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isRegularLocalRing_of_flat_formallyUnramified
-- name    : FunctorialResolution.EmbeddedResolution.isRegularLocalRing_of_flat_formallyUnramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:07:19.401082+00:00
-- url     : https://prove2.me/theorems/45ca1b3a-c9ee-48bb-a373-3ffe7f5f280a
-- title:
--   Embedded Resolution: is Regular Local Ring of flat formally Unramified
-- statement:
--   The Embedded Resolution construction uses the is Regular Local Ring of flat formally Unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean#L143-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean#L143-L167

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_RegularLocalRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.isRegularLocalRing_of_flat_formallyUnramified (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] [_root_.IsRegularLocalRing R] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]
    [Module.Flat R S] :
    _root_.IsRegularLocalRing S := by sorry
