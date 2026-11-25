-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_tors_and_isMonHom_of_cover
-- name    : GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:22.744581+00:00
-- url     : https://prove2.me/theorems/bc917d45-36a3-495d-a99f-b9c10f1ece82
-- title:
--   Cover Glue: tors and is Mon Hom of cover
-- statement:
--   The Cover Glue construction uses the tors and is Mon Hom of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionAndIsMonHomOfOpenCover.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionAndIsMonHomOfOpenCover.lean#L92-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionAndIsMonHomOfOpenCover
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
variable {S : Scheme.{0}} {I : Type} {U : I → S.Opens} {A : Over S} [GrpObj A] {G : ∀ i, Over (U i).toScheme}
  [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}

theorem GlobalTheory.CoverGlue.tors_and_isMonHom_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ (k : ℕ) (x : Out.baseOver S ⟶ A) (x' : ∀ i, Out.baseOver (U i).toScheme ⟶ G i), (∀ i, (x' i).left ≫ ψ i = (U i).ι ≫ x.left) → (∀ i, x' i ^ k = 1) → x ^ k = 1) ∧ ∀ (f : A ⟶ A) (f' : ∀ i, G i ⟶ G i), (∀ i, (f' i).left ≫ ψ i = ψ i ≫ f.left) → (∀ i, IsMonHom (f' i)) → IsMonHom f := by sorry
