-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_IsCocycle_swap
-- name    : GlobalTheory.AbLaw.CechOne.IsCocycle.swap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:34.00857+00:00
-- url     : https://prove2.me/theorems/891a6ab7-2ab6-4ae3-96d6-38d5ecd2be47
-- title:
--   Is Cocycle: swap
-- statement:
--   The Is Cocycle construction uses the swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L393-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L393-L398

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
variable {κ : Type} (D : κ → X.Opens)
variable [LinearOrder κ]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M)
variable {D f M}

theorem GlobalTheory.AbLaw.CechOne.IsCocycle.swap {I : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (a b : I) :
    φ a b = -restrict M (le_inf inf_le_right inf_le_left) (φ b a) := by sorry
