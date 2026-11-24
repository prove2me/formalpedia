-- Prove2me | Theorems.Thm_GlobalTheory_GrpFlatDesc_isAbelianScheme_of_flat_cover
-- name    : GlobalTheory.GrpFlatDesc.isAbelianScheme_of_flat_cover
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:42.352907+00:00
-- url     : https://prove2.me/theorems/d1548100-07fa-4d95-946e-e85909208085
-- title:
--   Grp Flat Desc: is Abelian Scheme of flat cover
-- statement:
--   The Grp Flat Desc construction uses the is Abelian Scheme of flat cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescends.lean#L122-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescends.lean#L122-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpFlatDesc
open GrpDense MorphismProperty
variable {Z U : Scheme.{0}}

theorem GlobalTheory.GrpFlatDesc.isAbelianScheme_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] [QuasiCompact j] (G : Over Z) (A : Over U)
    [GrpObj A] (hA : IsAbelianScheme A) (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G)
    (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G) (φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left) (h₂ : IsSquare φ φ₂)
    (hm : φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, IsAbelianScheme G ∧ IsGrpPullback A G j φ := by sorry
