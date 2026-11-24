-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isScalarTower_stalk
-- name    : FunctorialResolution.EmbeddedResolution.isScalarTower_stalk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:32.407466+00:00
-- url     : https://prove2.me/theorems/88c60139-13ee-4bc3-9b6c-2093f43f4267
-- title:
--   Embedded Resolution: is Scalar Tower stalk
-- statement:
--   The Embedded Resolution construction uses the is Scalar Tower stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L47-L55

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
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

theorem FunctorialResolution.EmbeddedResolution.isScalarTower_stalk (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (x : X) (hx : x ∈ U)
    [Algebra k Γ(X, U)] [Algebra k (X.presheaf.stalk x)] [Algebra Γ(X, U) (X.presheaf.stalk x)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hstalk : algebraMap k (X.presheaf.stalk x) = stalkAlgebraMap k p x)
    (hgerm : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom) :
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by sorry
