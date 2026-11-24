-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_exists_move_back
-- name    : GlobalTheory.FieldBaseChange.exists_move_back
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:49.355306+00:00
-- url     : https://prove2.me/theorems/66117ceb-67d8-49e3-9d86-a40215661e80
-- title:
--   Field Base Change: exists move back
-- statement:
--   The Field Base Change construction uses the exists move back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L122-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean#L122-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}

theorem GlobalTheory.FieldBaseChange.exists_move_back (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen)
    (m : Y' ⟶ Y) (k : ℤ) {g₂ : Z₂ ⟶ X₂} (h₂ : Y' ⟶ Z₂) (e₂ : h₂ ≫ g₂ = m ≫ f₂) {g₁ : Y' ⟶ X₁} (e₁ : g₁ = m ≫ f₁)
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => k))) :
    ∃ a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) i₂ i₁, f₂ (m (r z)) ∈ L₂.U i₂ → f₁ (m (r z)) ∈ L₁.U i₁ →
        powVal b (r ≫ h₂) z i₂ = (isoVal w (r ≫ m) z i₂ i₁ ^ k).val * powVal a r z i₁ := by sorry
