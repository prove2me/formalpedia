-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_exists_binary_op
-- name    : GlobalTheory.CoverGlue.exists_binary_op
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:46.399412+00:00
-- url     : https://prove2.me/theorems/87312775-018a-4361-81e1-0e9da72e3606
-- title:
--   Cover Glue: exists binary op
-- statement:
--   The Cover Glue construction uses the exists binary op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsBinaryOpGluedAlongCover.lean#L14-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsBinaryOpGluedAlongCover.lean#L14-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsBinaryOpGluedAlongCover
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

theorem GlobalTheory.CoverGlue.exists_binary_op : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) (ψ : ∀ i, (G i).left ⟶ A.left) (o : ∀ i, G i ⊗ G i ⟶ G i), iSup U = ⊤ → (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (lift x y ≫ o i).left ≫ ψ i = (lift x' y' ≫ o j).left ≫ ψ j) → ∃ m : A ⊗ A ⟶ A, ∀ i (T : Over (U i).toScheme) (x y : T ⟶ G i) (x₀ y₀ : Over.mk (T.hom ≫ (U i).ι) ⟶ A), x₀.left = x.left ≫ ψ i → y₀.left = y.left ≫ ψ i → (lift x₀ y₀ ≫ m).left = (lift x y ≫ o i).left ≫ ψ i := by sorry
