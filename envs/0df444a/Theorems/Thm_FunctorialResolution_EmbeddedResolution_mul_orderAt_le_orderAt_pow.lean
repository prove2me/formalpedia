-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mul_orderAt_le_orderAt_pow
-- name    : FunctorialResolution.EmbeddedResolution.mul_orderAt_le_orderAt_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:20.376894+00:00
-- url     : https://prove2.me/theorems/bc124b92-2d81-410b-b3a3-fdf7cafe6536
-- title:
--   Embedded Resolution: mul order At le order At pow
-- statement:
--   The Embedded Resolution construction uses the mul order At le order At pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L213-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L213-L216

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.mul_orderAt_le_orderAt_pow (I : X.IdealSheafData) (c : ℕ) (x : X) :
    (c : ℕ∞) * orderAt I x ≤ orderAt (I ^ c) x := by sorry
