-- Prove2me | Theorems.Thm_GlobalTheory_MulSupp_level
-- name    : GlobalTheory.MulSupp.level
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:03.55293+00:00
-- url     : https://prove2.me/theorems/6e3023de-aaea-5263-bdfb-16cc14745225
-- title:
--   Mul Supp: level
-- statement:
--   The Mul Supp construction uses the level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProductSupportInSubgroupTheta.lean#L90-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ProductSupportInSubgroupTheta.lean#L90-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqZeroOfThickeningsOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ProductSupportInSubgroupTheta
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
open GlobalTheory GlobalTheory.MulSupp
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable {D} {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.MulSupp.level {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G) (Λ : AddSubgroup D.X) (k l : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) (f) (f') (f'')
    (h : U.ExpT (𝟙_ _) k σ f) (h' : U.ExpT (𝟙_ _) l σ' f') (h'' : U.ExpT (𝟙_ _) (k + l) σ'' f'')
    (hm : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J →
      sval σ'' r z J = sval σ r z J * sval σ' r z J)
    (hf : ∀ α ∉ Λ, ∀ j, (f α).f j = 0) (hf' : ∀ α ∉ Λ, ∀ j, (f' α).f j = 0) (χ₀ : D.X) (hχ : χ₀ ∉ Λ) (e : ℕ)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left)
    (hr : r ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (f'' χ₀) r z J = 0 := by sorry
