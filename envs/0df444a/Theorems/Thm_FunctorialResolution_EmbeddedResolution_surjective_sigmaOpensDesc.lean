-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_surjective_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.surjective_sigmaOpensDesc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:12.903627+00:00
-- url     : https://prove2.me/theorems/5ddd20ff-ddca-435c-ac83-58f988c72ee2
-- title:
--   Embedded Resolution: surjective sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the surjective sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L82-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpens.lean#L82-L90

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u

theorem FunctorialResolution.EmbeddedResolution.surjective_sigmaOpensDesc (Y : Scheme.{u}) {ι : Type u} (U : ι → Y.Opens)
    (hU : iSup U = ⊤) : Surjective (sigmaOpensDesc Y U) := by sorry
