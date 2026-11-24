-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ
-- name    : FunctorialResolution.EmbeddedResolution.stalkIdeal_eq_map_germ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:00.844302+00:00
-- url     : https://prove2.me/theorems/ea75c2ec-ad07-467b-83a1-d93630a536e1
-- title:
--   Embedded Resolution: stalk Ideal eq map germ
-- statement:
--   The Embedded Resolution construction uses the stalk Ideal eq map germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L55-L65

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

theorem FunctorialResolution.EmbeddedResolution.stalkIdeal_eq_map_germ (I : X.IdealSheafData) (x : X) (U : X.affineOpens)
    (hx : x ∈ U.1) :
    stalkIdeal I x = Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by sorry
