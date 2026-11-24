-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_multiIndexDeriv_mul
-- name    : FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:09.18073+00:00
-- url     : https://prove2.me/theorems/d3cf35bf-d67a-404c-819d-d8f4c4fa0d71
-- title:
--   Embedded Resolution: multi Index Deriv mul
-- statement:
--   The Embedded Resolution construction uses the multi Index Deriv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L258-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/MultiIndexDerivation.lean#L258-L316

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

theorem FunctorialResolution.EmbeddedResolution.multiIndexDeriv_mul {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (f g : R) :
    multiIndexDeriv D α (f * g) =
      ∑ β ∈ Fintype.piFinset fun i => Finset.range (α i + 1),
        ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g := by sorry
