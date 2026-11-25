-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CechOne_exists_kill
-- name    : GlobalTheory.AbLaw.CechOne.exists_kill
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:29.468802+00:00
-- url     : https://prove2.me/theorems/7fcef271-5e06-5107-915b-9465fc9f68cf
-- title:
--   Cech One: exists kill
-- statement:
--   The Cech One construction uses the exists kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L184-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CechHOneVanishesOnOpenOfIsAffineOpen.lean#L184-L200

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

theorem GlobalTheory.AbLaw.CechOne.exists_kill (hM : M.IsLB) {V U W : X.Opens} (hU : IsAffineOpen U) (hUV : U ≤ V) (i : M.ι)
    (hi : U ≤ M.U i) (t : Γ(X, V)) (hW : W = U ⊓ X.basicOpen t) (φ : SecOn M U)
    (h : restrict M (hW.le.trans inf_le_left) φ = 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → rs X hUV t ^ n • φ = 0 := by sorry
