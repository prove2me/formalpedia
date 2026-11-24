-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_algebraMap_stalkAlgebra
-- name    : FunctorialResolution.EmbeddedResolution.algebraMap_stalkAlgebra
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:33.454861+00:00
-- url     : https://prove2.me/theorems/67bd6686-252d-4039-bf66-76bdb177ae1f
-- title:
--   Embedded Resolution: algebra Map stalk Algebra
-- statement:
--   The Embedded Resolution construction uses the algebra Map stalk Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/DerivativeIdealSheafOrderDecrease.lean#L23-L26

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

theorem FunctorialResolution.EmbeddedResolution.algebraMap_stalkAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    @algebraMap k (X.presheaf.stalk x) _ _ (stalkAlgebra k p x) = stalkAlgebraMap k p x := by sorry
