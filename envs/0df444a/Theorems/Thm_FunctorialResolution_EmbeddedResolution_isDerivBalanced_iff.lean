-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isDerivBalanced_iff
-- name    : FunctorialResolution.EmbeddedResolution.isDerivBalanced_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:16:06.541612+00:00
-- url     : https://prove2.me/theorems/b385d714-e1b0-4fbb-b34e-28eb555ce844
-- title:
--   Embedded Resolution: is Deriv Balanced iff
-- statement:
--   The Embedded Resolution construction uses the is Deriv Balanced iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L16-L18

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

theorem FunctorialResolution.EmbeddedResolution.isDerivBalanced_iff (I : X.IdealSheafData) (m : ℕ) :
    IsDerivBalanced k p I m ↔ ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i) := by sorry
