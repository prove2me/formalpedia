-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_isOpen_connectedComponent_of_noetherianSpace
-- name    : FunctorialResolution.Blowup.isOpen_connectedComponent_of_noetherianSpace
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:28.579038+00:00
-- url     : https://prove2.me/theorems/a6b5cc14-0c3c-4a77-a25a-7bd52444364d
-- title:
--   Blowup: is Open connected Component of noetherian Space
-- statement:
--   The Blowup construction uses the is Open connected Component of noetherian Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L86-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Schemes/SchemeMorphismProperties.lean#L86-L113

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

theorem FunctorialResolution.Blowup.isOpen_connectedComponent_of_noetherianSpace (T : Type v) [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] (x : T) : IsOpen (connectedComponent x) := by sorry
