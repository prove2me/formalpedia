-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_kerEquiv_val
-- name    : GlobalTheory.AbLaw.CechOne.kerEquiv_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:34:59.37843+00:00
-- url     : https://prove2.me/theorems/71b8beb8-636e-4b90-b7b0-9f5dbd8ac42f
-- title:
--   Cech One: ker Equiv val
-- statement:
--   The Cech One construction uses the ker Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L565-L566
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L565-L566

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

theorem GlobalTheory.AbLaw.CechOne.kerEquiv_val {V : X.Opens} (hD : ∀ i, D i ≤ V) (hc : V ≤ ⨆ i, D i)
    (x : SecOnR f M V) : (kerEquiv M f hD hc x).1 = toCech M f D hD x := by sorry

attribute [defeq] GlobalTheory.AbLaw.CechOne.kerEquiv_val
