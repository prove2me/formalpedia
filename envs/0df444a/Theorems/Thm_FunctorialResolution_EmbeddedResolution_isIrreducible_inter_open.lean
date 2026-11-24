-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isIrreducible_inter_open
-- name    : FunctorialResolution.EmbeddedResolution.isIrreducible_inter_open
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:47:51.473049+00:00
-- url     : https://prove2.me/theorems/79b312d0-d0ec-4b93-afdc-84e2809e4472
-- title:
--   Embedded Resolution: is Irreducible inter open
-- statement:
--   The Embedded Resolution construction uses the is Irreducible inter open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/GenericPointImage.lean#L25-L31

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

theorem FunctorialResolution.EmbeddedResolution.isIrreducible_inter_open {S U : Set X} (hS : IsIrreducible S) (hU : IsOpen U)
    (hne : (S ∩ U).Nonempty) : IsIrreducible (S ∩ U) := by sorry
