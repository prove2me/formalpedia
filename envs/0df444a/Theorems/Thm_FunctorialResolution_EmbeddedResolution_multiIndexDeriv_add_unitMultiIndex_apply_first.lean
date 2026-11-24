-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_add_unitMultiIndex_apply_first
-- name    : FunctorialResolution.EmbeddedResolution.multiIndexDeriv_add_unitMultiIndex_apply_first
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:05.82074+00:00
-- url     : https://prove2.me/theorems/62fb8a49-2e3a-4321-ae47-adb727d57866
-- title:
--   Embedded Resolution: multi Index Deriv add unit Multi Index apply first
-- statement:
--   The Embedded Resolution construction uses the multi Index Deriv add unit Multi Index apply first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L469-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L469-L472

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

theorem FunctorialResolution.EmbeddedResolution.multiIndexDeriv_add_unitMultiIndex_apply_first {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α : Fin h → ℕ) (i : Fin h) (x : R) :
    multiIndexDeriv D (α + unitMultiIndex i) x = multiIndexDeriv D α (D i x) := by sorry
