-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- name    : FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:39.04438+00:00
-- url     : https://prove2.me/theorems/1e54c3cb-d4a4-44ac-8492-bf65d93587aa
-- title:
--   Embedded Resolution: unit Multi Index apply
-- statement:
--   The Embedded Resolution construction uses the unit Multi Index apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L421-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L421-L422

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

theorem FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply {h : ℕ} (i j : Fin h) :
    unitMultiIndex i j = if j = i then 1 else 0 := by sorry

attribute [defeq] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply
