-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_stalkIdeal
-- name    : FunctorialResolution.EmbeddedResolution.germ_mem_stalkIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:24.814408+00:00
-- url     : https://prove2.me/theorems/05903fc8-699e-4a6d-a483-daf02f12ca3f
-- title:
--   Embedded Resolution: germ mem stalk Ideal
-- statement:
--   The Embedded Resolution construction uses the germ mem stalk Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/IdealSheafOrder.lean#L67-L73

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

theorem FunctorialResolution.EmbeddedResolution.germ_mem_stalkIdeal (I : X.IdealSheafData) (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    {s : Γ(X, U.1)} (hs : s ∈ I.ideal U) :
    (X.presheaf.germ U.1 x hx).hom s ∈ stalkIdeal I x := by sorry
