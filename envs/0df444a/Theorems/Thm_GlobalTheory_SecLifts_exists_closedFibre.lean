-- Prove2me | Theorems.Thm_GlobalTheory_SecLifts_exists_closedFibre
-- name    : GlobalTheory.SecLifts.exists_closedFibre
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:22.994988+00:00
-- url     : https://prove2.me/theorems/8d79b97b-628d-41ec-88e3-ceaa7b6e35bc
-- title:
--   Sec Lifts: exists closed Fibre
-- statement:
--   The Sec Lifts construction uses the exists closed Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompatibleSections.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsCompatibleSections.lean#L14-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompatibleSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecLifts

theorem GlobalTheory.SecLifts.exists_closedFibre (V : Type) [CommRing V] (I : Ideal V)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V I e))
    (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
    (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (e : ℕ) :
    ∃ j : (Y 0).left ⟶ (Y (e + 1)).left,
      IsPullback j (Y 0).hom (Y (e + 1)).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (by omega) : I ^ (e + 1 + 1) ≤ I ^ (0 + 1))))) ∧
      ∃ w : LB.Iso (N 0) ((N (e + 1)).pull j), w.IsGen := by sorry
