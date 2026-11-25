-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_IsCocycle_diag
-- name    : GlobalTheory.AbLaw.CechOne.IsCocycle.diag
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:03.207993+00:00
-- url     : https://prove2.me/theorems/51446091-63e3-475a-ae68-1c5c689a9199
-- title:
--   Is Cocycle: diag
-- statement:
--   The Is Cocycle construction uses the diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L387-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L387-L391

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

theorem GlobalTheory.AbLaw.CechOne.IsCocycle.diag {I : Type} {O : I → X.Opens} {φ : ∀ a b, SecOn M (O a ⊓ O b)}
    (hφ : IsCocycle M O φ) (a : I) : φ a a = 0 := by sorry
