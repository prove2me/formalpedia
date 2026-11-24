-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_closure_inter_open_eq
-- name    : FunctorialResolution.EmbeddedResolution.closure_inter_open_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:39.849801+00:00
-- url     : https://prove2.me/theorems/5e72e723-e87d-44dc-8163-1ef8523e6a77
-- title:
--   Embedded Resolution: closure inter open eq
-- statement:
--   The Embedded Resolution construction uses the closure inter open eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L33-L41

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem FunctorialResolution.EmbeddedResolution.closure_inter_open_eq {S U : Set X} (hS : IsClosed S) (hirr : IsIrreducible S)
    (hU : IsOpen U) (hne : (S ∩ U).Nonempty) : closure (S ∩ U) = S := by sorry
