-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsDerivBalanced_derivIdealSheafIterate_pow_le
-- name    : FunctorialResolution.EmbeddedResolution.IsDerivBalanced.derivIdealSheafIterate_pow_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:16:40.385357+00:00
-- url     : https://prove2.me/theorems/8e4027d0-501c-418a-8b83-e1427c21a6c4
-- title:
--   Is Deriv Balanced: deriv Ideal Sheaf Iterate pow le
-- statement:
--   The Is Deriv Balanced construction uses the deriv Ideal Sheaf Iterate pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L20-L22

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
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
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

theorem FunctorialResolution.EmbeddedResolution.IsDerivBalanced.derivIdealSheafIterate_pow_le {I : X.IdealSheafData} {m : ℕ} (h : IsDerivBalanced k p I m)
    {i : ℕ} (hi : i < m) : derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) := by sorry
