-- Prove2me | Theorems.Thm_GlobalTheory_CocycleGlue_exists_glue
-- name    : GlobalTheory.CocycleGlue.exists_glue
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:15:50.159462+00:00
-- url     : https://prove2.me/theorems/4ad82f02-bc92-4857-b2ff-5b94ba9aad3d
-- title:
--   Cocycle Glue: exists glue
-- statement:
--   The Cocycle Glue construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GlueSchemesOverOpensAlongCocycle.lean#L24-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GlueSchemesOverOpensAlongCocycle.lean#L24-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GlueSchemesOverOpensAlongCocycle
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
open GlobalTheory GlobalTheory.CocycleGlue

theorem GlobalTheory.CocycleGlue.exists_glue {S : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S)
    (hκ : ∀ i, IsOpenImmersion (κ i)) (g : ∀ i, X i ⟶ V i) (B : I → I → Scheme.{0})
    (a : ∀ i j, B i j ⟶ X i) (b : ∀ i j, B i j ⟶ X j)
    (ha : ∀ i j, IsPullback (a i j) (b i j ≫ g j) (g i ≫ κ i) (κ j))
    (hb : ∀ i j, IsPullback (b i j) (a i j ≫ g i) (g j ≫ κ j) (κ i))
    (hc : ∀ i j k (T : Scheme.{0}) (x : T ⟶ B i j) (y : T ⟶ B j k) (z : T ⟶ B i k),
      x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) :
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by sorry
