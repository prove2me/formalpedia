-- Prove2me | Theorems.Thm_GlobalTheory_GrpFlatDesc_grpObj_of_flat_cover
-- name    : GlobalTheory.GrpFlatDesc.grpObj_of_flat_cover
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:58:23.4818+00:00
-- url     : https://prove2.me/theorems/fb2e8804-a70f-4517-b68c-2e330c7274fc
-- title:
--   Grp Flat Desc: grp Obj of flat cover
-- statement:
--   The Grp Flat Desc construction uses the grp Obj of flat cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescends.lean#L72-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescends.lean#L72-L120

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

theorem GlobalTheory.GrpFlatDesc.grpObj_of_flat_cover (j : U ⟶ Z) [Flat j] [Surjective j] (G : Over Z) (A : Over U) [GrpObj A]
    [IsCommMonObj A] (φ : A.left ⟶ G.left) (h : IsPullback φ A.hom G.hom j) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (e : 𝟙_ (Over Z) ⟶ G)
    (hm : ∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ)
    (hi : φ ≫ i.left = (ι[A]).left ≫ φ) (he : j ≫ e.left = (η[A]).left ≫ φ) :
    ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by sorry
