-- Prove2me | Theorems.Thm_GlobalTheory_semiAbelian_rigidity
-- name    : GlobalTheory.semiAbelian_rigidity
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:26:38.003428+00:00
-- url     : https://prove2.me/theorems/356a0366-103e-41ce-a15b-6347b2e4be28
-- title:
--   Global Theory: semi Abelian rigidity
-- statement:
--   The Global Theory construction uses the semi Abelian rigidity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean#L471-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsTorusAndQuotientHom.lean#L471-L497

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SemiRigid

theorem GlobalTheory.semiAbelian_rigidity :
    (∀ (K : Type) [Field K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B →
      ∀ f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B,
        (∃ b : 𝟙_ _ ⟶ B, f = toUnit _ ≫ b) ∧ (IsMonHom f → f = toUnit _ ≫ η[B])) ∧
    (∀ (K : Type) [Field K] (G H : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj H],
      Nonempty (TorusExtension G) → Nonempty (TorusExtension H) →
      (∀ f : G ⊗ G ⟶ H, lift (𝟙 G) (toUnit G ≫ η[G]) ≫ f = toUnit G ≫ η[H] →
        lift (toUnit G ≫ η[G]) (𝟙 G) ≫ f = toUnit G ≫ η[H] → f = toUnit _ ≫ η[H]) ∧
      ∀ φ : G ⟶ H, η[G] ≫ φ = η[H] → IsMonHom φ) ∧
    (∀ (S : Scheme.{0}) [IsReduced S] (G H : Over S) [GrpObj G] [GrpObj H],
      IsSemiAbelian G → IsSemiAbelian H →
      (∀ f : G ⊗ G ⟶ H, lift (𝟙 G) (toUnit G ≫ η[G]) ≫ f = toUnit G ≫ η[H] →
        lift (toUnit G ≫ η[G]) (𝟙 G) ≫ f = toUnit G ≫ η[H] → f = toUnit _ ≫ η[H]) ∧
      ∀ φ : G ⟶ H, η[G] ≫ φ = η[H] → IsMonHom φ) ∧
    (∀ (K : Type) [Field K] (G H : Over (Spec (CommRingCat.of K))) [GrpObj G] [GrpObj H]
      (D : TorusExtension G) (E : TorusExtension H) (φ : G ⟶ H), IsMonHom φ →
      letI := D.addCommGroup; letI := E.addCommGroup; letI := D.grpB; letI := E.grpB
      (∃! α : splitTorus (Spec (CommRingCat.of K)) D.X ⟶ splitTorus (Spec (CommRingCat.of K)) E.X,
        IsMonHom α ∧ α ≫ E.i = D.i ≫ φ) ∧
      (∃! β : D.B ⟶ E.B, IsMonHom β ∧ D.q ≫ β = φ ≫ E.q)) := by sorry
