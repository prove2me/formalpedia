-- Prove2me | Theorems.Thm_GlobalTheory_UU_gs_scal_inv_mul
-- name    : GlobalTheory.UU.gs_scal_inv_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:54.690861+00:00
-- url     : https://prove2.me/theorems/131daaf7-7ad4-44b2-91db-0d13cf82005b
-- title:
--   UU: gs scal inv mul
-- statement:
--   The UU construction uses the gs scal inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValueExpansionOfChartExpansion.lean#L44-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ValueExpansionOfChartExpansion.lean#L44-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpTOfExpandsAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValueExpansionOfChartExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU

theorem GlobalTheory.UU.gs_scal_inv_mul {R : Type} [CommRing R] [IsDomain R] {Y₁ Y₂ Z : Scheme.{0}}
    (p₁ : Y₁ ⟶ Spec (CommRingCat.of (FractionRing R))) (p₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (r₁ : Z ⟶ Y₁) (r₂ : Z ⟶ Y₂) (h : r₂ ≫ p₂ = ((r₁ ≫ p₁) ≫ jFK (R := R) (FractionRing R)) ≫ jK R) (z : Z)
    {a : R} (ha : a ≠ 0) :
    gs r₁ z ⊤ (scal p₁ (algebraMap R (FractionRing R) a)⁻¹) * gs r₂ z ⊤ (scal p₂ a) = 1 := by sorry
