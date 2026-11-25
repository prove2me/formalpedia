-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_secKerEquiv_val
-- name    : GlobalTheory.AbLaw.CechOne.secKerEquiv_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:30.877645+00:00
-- url     : https://prove2.me/theorems/96539e07-e8d7-40fb-9f5c-5bd9180cac73
-- title:
--   Cech One: sec Ker Equiv val
-- statement:
--   The Cech One construction uses the sec Ker Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L572-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L572-L574

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CechHOneVanishesOnOpenOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CechOne
open SecOn
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable {M : LB X}
variable {κ : Type} [LinearOrder κ] (f : X ⟶ Spec (CommRingCat.of R)) (M) (D : κ → X.Opens)
variable {D}

theorem GlobalTheory.AbLaw.CechOne.secKerEquiv_val (hc : ⨆ i, D i = ⊤) (σ : LB.Sec M) (s : {s : Finset κ // s.card = 0 + 1}) :
    (secKerEquiv M f hc σ).1 s = SecOnR.of f M _ (GlobalTheory.LB.ofSec σ (⨅ i ∈ s.1, D i)) := by sorry
