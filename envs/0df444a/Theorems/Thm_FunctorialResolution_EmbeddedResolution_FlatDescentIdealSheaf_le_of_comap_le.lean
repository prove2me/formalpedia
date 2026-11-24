-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_FlatDescentIdealSheaf_le_of_comap_le
-- name    : FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf.le_of_comap_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:46:11.371157+00:00
-- url     : https://prove2.me/theorems/3a8daa3f-2e55-4094-9d24-42bdd5bfe6ce
-- title:
--   Flat Descent Ideal Sheaf: le of comap le
-- statement:
--   The Flat Descent Ideal Sheaf construction uses the le of comap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatComapInjective.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/IdealSheafFlatComapInjective.lean#L153-L163

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

theorem FunctorialResolution.EmbeddedResolution.FlatDescentIdealSheaf.le_of_comap_le (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.Surjective g] (I J : Y.IdealSheafData)
    (h : I.comap g ≤ J.comap g) : I ≤ J := by sorry
