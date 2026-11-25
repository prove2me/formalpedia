-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_d_two_apply_triple
-- name    : GlobalTheory.AbLaw.CechOne.d_two_apply_triple
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:43:52.913969+00:00
-- url     : https://prove2.me/theorems/5bcb39a0-7c24-56a5-bf87-491493ef6015
-- title:
--   Cech One: d two apply triple
-- statement:
--   The Cech One construction uses the d two apply triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L305-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L305-L336

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

theorem GlobalTheory.AbLaw.CechOne.d_two_apply_triple {κ : Type} [LinearOrder κ] (A : GlobalTheory.Cube.{0} κ R) (x : GlobalTheory.Cube.Term A 2)
    {i j k : κ} (h : i < j) (h' : j < k) (hc : ({i, j, k} : Finset κ).card = 2 + 1) :
    GlobalTheory.Cube.d A 2 x ⟨{i, j, k}, hc⟩ =
      GlobalTheory.Cube.res A (by simp) (x ⟨{j, k}, Finset.card_pair h'.ne⟩) -
        GlobalTheory.Cube.res A (by simp) (x ⟨{i, k}, Finset.card_pair (h.trans h').ne⟩) +
        GlobalTheory.Cube.res A (by simp [Finset.insert_subset_iff]) (x ⟨{i, j}, Finset.card_pair h.ne⟩) := by sorry
