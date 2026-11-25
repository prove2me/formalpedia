-- Prove2me | Theorems.Thm_GlobalTheory_LevelVanishing_main
-- name    : GlobalTheory.LevelVanishing.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:12:42.982288+00:00
-- url     : https://prove2.me/theorems/475aec2f-abae-551f-afae-d04c51fed172
-- title:
--   Level Vanishing: main
-- statement:
--   The Level Vanishing construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FromSpecStalkComp.lean#L65-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FromSpecStalkComp.lean#L65-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FromSpecStalkComp
import Theorems.Thm_GlobalTheory_LiftTest_main
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
open GlobalTheory GlobalTheory.LevelVanishing

theorem GlobalTheory.LevelVanishing.main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) f, U.ExpT (𝟙_ _) k σ f → ∀ e : ℕ, ∃ s : Finset D.X, ∀ α ∉ s, ∀ (z : (𝟙_ _ ⊗ D.P.A).left) (J), Good D.P.L z J → sval (f α) (𝟙 _) z J ∈ (IsLocalRing.maximalIdeal V ^ (e + 1)).map (((𝟙_ _ ⊗ D.P.A).left.presheaf.germ ⊤ z trivial).hom.comp (((𝟙_ _ ⊗ D.P.A).hom.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom))) := by sorry
