-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_pow_succ_le
-- name    : FunctorialResolution.EmbeddedResolution.derivIdealSheaf_pow_succ_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:59:41.105467+00:00
-- url     : https://prove2.me/theorems/845822d0-5e8e-4034-a846-b6922a7e1e8e
-- title:
--   Embedded Resolution: deriv Ideal Sheaf pow succ le
-- statement:
--   The Embedded Resolution construction uses the deriv Ideal Sheaf pow succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L184-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheaf.lean#L184-L197

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.derivIdealSheaf_pow_succ_le (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) (n : ℕ) :
    derivIdealSheaf k p (I ^ (n + 1)) ≤ I ^ n * derivIdealSheaf k p I := by sorry
