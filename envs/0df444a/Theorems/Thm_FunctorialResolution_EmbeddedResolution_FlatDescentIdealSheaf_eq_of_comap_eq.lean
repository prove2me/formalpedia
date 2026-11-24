-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_FlatDescentIdealSheaf_eq_of_comap_eq
-- name    : FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf.eq_of_comap_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:45:21.837801+00:00
-- url     : https://prove2.me/theorems/31d7791d-9928-4461-94f4-dbefb112f8b4
-- title:
--   Flat Descent Ideal Sheaf: eq of comap eq
-- statement:
--   The Flat Descent Ideal Sheaf construction uses the eq of comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatComapInjective.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatComapInjective.lean#L165-L168

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatComapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf
variable {W Y : Scheme.{u}}

theorem FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf.eq_of_comap_eq (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g = J.comap g) : I = J := by sorry
