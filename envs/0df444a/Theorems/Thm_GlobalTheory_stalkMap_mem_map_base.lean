-- Prove2me | Theorems.Thm_GlobalTheory_stalkMap_mem_map_base
-- name    : GlobalTheory.stalkMap_mem_map_base
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:26:03.891687+00:00
-- url     : https://prove2.me/theorems/56760fb3-4598-5f51-b9db-6366b1fe68fb
-- title:
--   Global Theory: stalk Map mem map base
-- statement:
--   The Global Theory construction uses the stalk Map mem map base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsOrderTranslates.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsOrderTranslates.lean#L19-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsOrderTranslates
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open GlobalTheory

theorem GlobalTheory.stalkMap_mem_map_base {R : Type} [CommRing R] (I : Ideal R) {Z Z' : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of R)) (p' : Z' ⟶ Spec (CommRingCat.of R)) (ρ : Z' ⟶ Z) (h : ρ ≫ p = p') (z : Z')
    (a : Z.presheaf.stalk (ρ z))
    (ha : a ∈ I.map ((Z.presheaf.germ ⊤ (ρ z) trivial).hom.comp
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))) :
    (ρ.stalkMap z).hom a ∈ I.map ((Z'.presheaf.germ ⊤ z trivial).hom.comp
      (p'.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) := by sorry
