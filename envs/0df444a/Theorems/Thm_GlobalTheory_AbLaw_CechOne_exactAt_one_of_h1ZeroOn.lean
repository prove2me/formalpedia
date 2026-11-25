-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_exactAt_one_of_h1ZeroOn
-- name    : GlobalTheory.AbLaw.CechOne.exactAt_one_of_h1ZeroOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:03.542711+00:00
-- url     : https://prove2.me/theorems/ae0162f0-afcb-442d-a1c0-c991cc7b5365
-- title:
--   Cech One: exact At one of h1 Zero On
-- statement:
--   The Cech One construction uses the exact At one of h1 Zero On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L584-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L584-L586

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
variable {M}

theorem GlobalTheory.AbLaw.CechOne.exactAt_one_of_h1ZeroOn {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i)
    (h : CechHOneVanishesOnOpen M V) : (cechLB f M D).ExactAt 1 := by sorry
