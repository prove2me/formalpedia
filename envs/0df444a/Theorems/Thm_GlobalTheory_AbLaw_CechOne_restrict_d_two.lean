-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_restrict_d_two
-- name    : GlobalTheory.AbLaw.CechOne.restrict_d_two
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:36:32.149303+00:00
-- url     : https://prove2.me/theorems/a0a2ea5b-934c-4f57-8138-3f2b23b72013
-- title:
--   Cech One: restrict d two
-- statement:
--   The Cech One construction uses the restrict d two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L371-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L371-L385

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
variable {κ : Type} (D : κ → X.Opens)
variable [LinearOrder κ]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M)
variable {D f M}

theorem GlobalTheory.AbLaw.CechOne.restrict_d_two (x : GlobalTheory.Cube.Term (secCube f M D) 2) {i j k : κ} (h : i < j) (h' : j < k)
    (hc : ({i, j, k} : Finset κ).card = 2 + 1) {W : X.Opens}
    (hi : W ≤ D i) (hj : W ≤ D j) (hk : W ≤ D k) :
    restrict M (by simp [hi, hj, hk]) (comp M D f (GlobalTheory.Cube.d _ 2 x) {i, j, k} hc) =
      restrict M (le_pair D hj hk) (comp M D f x {j, k} (Finset.card_pair h'.ne)) -
        restrict M (le_pair D hi hk) (comp M D f x {i, k} (Finset.card_pair (h.trans h').ne)) +
        restrict M (le_pair D hi hj) (comp M D f x {i, j} (Finset.card_pair h.ne)) := by sorry
