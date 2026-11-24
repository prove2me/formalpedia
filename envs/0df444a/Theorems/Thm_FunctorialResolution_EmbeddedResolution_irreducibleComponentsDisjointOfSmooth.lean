-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_irreducibleComponentsDisjointOfSmooth
-- name    : FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:46.321833+00:00
-- url     : https://prove2.me/theorems/df8c6f35-df6b-4d92-aac0-6e33b00d9883
-- title:
--   Embedded Resolution: irreducible Components Disjoint Of Smooth
-- statement:
--   The Embedded Resolution construction uses the irreducible Components Disjoint Of Smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/SmoothComponentsDisjoint.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/MarkedBlowupSequence/SmoothComponentsDisjoint.lean#L16-L23

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_IrreducibleComponents
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_SmoothComponentsDisjoint
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

theorem FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth : IrreducibleComponentsDisjointOfSmooth.{u} := by sorry
