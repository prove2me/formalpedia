-- Prove2me | Theorems.Thm_GlobalTheory_grpObj_of_dense_open
-- name    : GlobalTheory.grpObj_of_dense_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:36.009814+00:00
-- url     : https://prove2.me/theorems/832d4d63-1afd-4cbe-a2ea-211c80742cae
-- title:
--   Global Theory: grp Obj of dense open
-- statement:
--   The Global Theory construction uses the grp Obj of dense open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpObjOfDenseOpen.lean#L111-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GrpObjOfDenseOpen.lean#L111-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
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
open GlobalTheory
open GrpDense

theorem GlobalTheory.grpObj_of_dense_open :
    ∀ (Z U : Scheme.{0}) [IsIntegral Z] [Nonempty U] (j : U ⟶ Z) [IsOpenImmersion j] (G : Over Z) [Smooth G.hom]
      [IsSeparated G.hom] (A : Over U) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left),
      IsPullback φ A.hom G.hom j → ∀ (m : G ⊗ G ⟶ G) (i : G ⟶ G) (e : 𝟙_ (Over Z) ⟶ G),
      (∀ φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → j ≫ e.left = (η[A]).left ≫ φ →
      ∃ _ : GrpObj G, μ[G] = m ∧ η[G] = e ∧ ι[G] = i ∧ IsCommMonObj G ∧ IsGrpPullback A G j φ := by sorry
