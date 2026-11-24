-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_isPullback_of_comp_mono
-- name    : GlobalTheory.ZJ.isPullback_of_comp_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:29.539809+00:00
-- url     : https://prove2.me/theorems/426e9ce9-2d7a-437e-a2bd-9f581e9ae308
-- title:
--   ZJ: is Pullback of comp mono
-- statement:
--   The ZJ construction uses the is Pullback of comp mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TestCartOfSpecialFibreSurjective.lean#L102-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ

theorem GlobalTheory.ZJ.isPullback_of_comp_mono {𝒞 : Type*} [Category 𝒞] {A G P U Z : 𝒞} {a : A ⟶ G} {i : G ⟶ P} [Mono i]
    {s : A ⟶ U} {t : P ⟶ Z} {u : U ⟶ Z} (h : IsPullback (a ≫ i) s t u) : IsPullback a s (i ≫ t) u := by sorry
