-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isDerivBalanced_of_pow_le
-- name    : FunctorialResolution.EmbeddedResolution.isDerivBalanced_of_pow_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:25.07675+00:00
-- url     : https://prove2.me/theorems/753011aa-7f8e-570e-9a47-b5ffafa8d3ab
-- title:
--   Embedded Resolution: is Deriv Balanced of pow le
-- statement:
--   The Embedded Resolution construction uses the is Deriv Balanced of pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactIdeal.lean#L24-L26

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

theorem FunctorialResolution.EmbeddedResolution.isDerivBalanced_of_pow_le {I : X.IdealSheafData} {m : ℕ}
    (h : ∀ i < m, derivIdealSheafIterate k p i I ^ m ≤ I ^ (m - i)) : IsDerivBalanced k p I m := by sorry
