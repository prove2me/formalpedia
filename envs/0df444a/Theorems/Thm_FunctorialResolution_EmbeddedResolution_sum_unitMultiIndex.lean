-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_sum_unitMultiIndex
-- name    : FunctorialResolution.EmbeddedResolution.sum_unitMultiIndex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:01.23188+00:00
-- url     : https://prove2.me/theorems/912c215e-db11-4343-a414-bd9df472f9a3
-- title:
--   Embedded Resolution: sum unit Multi Index
-- statement:
--   The Embedded Resolution construction uses the sum unit Multi Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L424-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L424-L425

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem FunctorialResolution.EmbeddedResolution.sum_unitMultiIndex {h : ℕ} (i : Fin h) : ∑ j, unitMultiIndex i j = 1 := by sorry
