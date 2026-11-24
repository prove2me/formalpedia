-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_unitMultiIndex
-- name    : FunctorialResolution.EmbeddedResolution.multiIndexDeriv_unitMultiIndex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:56.836324+00:00
-- url     : https://prove2.me/theorems/777a52c8-f440-4909-9dd0-5099a2f5fc52
-- title:
--   Embedded Resolution: multi Index Deriv unit Multi Index
-- statement:
--   The Embedded Resolution construction uses the multi Index Deriv unit Multi Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L459-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L459-L467

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

theorem FunctorialResolution.EmbeddedResolution.multiIndexDeriv_unitMultiIndex {h : ℕ} (D : Fin h → Derivation k R R) (i : Fin h) (x : R) :
    multiIndexDeriv D (unitMultiIndex i) x = D i x := by sorry
