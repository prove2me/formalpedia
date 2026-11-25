-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isClopen_irreducibleComponent_of_smooth
-- name    : FunctorialResolution.EmbeddedResolution.isClopen_irreducibleComponent_of_smooth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:38.466623+00:00
-- url     : https://prove2.me/theorems/bef1da75-719b-45a8-bac4-a9c317b7aca1
-- title:
--   Embedded Resolution: is Clopen irreducible Component of smooth
-- statement:
--   The Embedded Resolution construction uses the is Clopen irreducible Component of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean#L460-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean#L460-L472

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

theorem FunctorialResolution.EmbeddedResolution.isClopen_irreducibleComponent_of_smooth {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (hp : AlgebraicGeometry.Smooth p)
    {T : Set ↥X} (hT : T ∈ irreducibleComponents ↥X) : IsClopen T := by sorry
