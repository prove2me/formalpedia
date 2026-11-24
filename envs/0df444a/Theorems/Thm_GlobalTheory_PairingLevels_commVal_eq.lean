-- Prove2me | Theorems.Thm_GlobalTheory_PairingLevels_commVal_eq
-- name    : GlobalTheory.PairingLevels.commVal_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:57.916992+00:00
-- url     : https://prove2.me/theorems/26b588b6-cd9f-45dc-acd3-9a4b2e0f988e
-- title:
--   Pairing Levels: comm Val eq
-- statement:
--   The Pairing Levels construction uses the comm Val eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L146-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L146-L205

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}

theorem GlobalTheory.PairingLevels.commVal_eq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {t : LB.Gen (Theta A L)} (ht : t.IsGen)
    {k : ℤ} {l : ℕ} {T T' Z : Over S} (χ φ' : ThetaGrp A L (k * l) T) (ψ φ : ThetaGrp A L k T') (s : Z ⟶ T)
    (s' : Z ⟶ T') (hx : s' ≫ ψ.pt = (s ≫ χ.pt) ^ l) (hy : s' ≫ φ.pt = s ≫ φ'.pt) {z : Z.left} {J}
    (hJ : Good L z J) : commVal χ φ' s 1 z J = commVal ψ φ s' 1 z J := by sorry
