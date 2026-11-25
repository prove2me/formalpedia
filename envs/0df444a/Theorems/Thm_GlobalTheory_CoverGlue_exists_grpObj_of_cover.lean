-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_exists_grpObj_of_cover
-- name    : GlobalTheory.CoverGlue.exists_grpObj_of_cover
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:28.621721+00:00
-- url     : https://prove2.me/theorems/ba506de3-a6cc-43ae-b27f-6c77f39830a9
-- title:
--   Cover Glue: exists grp Obj of cover
-- statement:
--   The Cover Glue construction uses the exists grp Obj of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGrpObjOfLocalGroupLawsOnCover.lean#L14-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGrpObjOfLocalGroupLawsOnCover.lean#L14-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGrpObjOfLocalGroupLawsOnCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue

theorem GlobalTheory.CoverGlue.exists_grpObj_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (m n : A ⊗ A ⟶ A) (e : Out.baseOver S ⟶ A), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (x * y).left ≫ ψ i ∧ (lift x₀ y₀ ≫ n).left = (x⁻¹).left ≫ ψ i) → (∀ i, (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = (U i).ι ≫ e.left) → ∃ _ : GrpObj A, ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i) := by sorry
