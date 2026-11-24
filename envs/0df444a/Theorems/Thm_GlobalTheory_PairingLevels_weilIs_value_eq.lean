-- Prove2me | Theorems.Thm_GlobalTheory_PairingLevels_weilIs_value_eq
-- name    : GlobalTheory.PairingLevels.weilIs_value_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:09.506008+00:00
-- url     : https://prove2.me/theorems/fc109e05-1d99-45bc-99ec-e44fdfa3a8cf
-- title:
--   Pairing Levels: weil Is value eq
-- statement:
--   The Pairing Levels construction uses the weil Is value eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L207-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsValueEq.lean#L207-L225

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

theorem GlobalTheory.PairingLevels.weilIs_value_eq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {t : LB.Gen (Theta A L)}
    (ht : t.IsGen) {k : ℤ} {l : ℕ} {T : Over S} {x y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : WeilIs A L (k * l) x y c) (h' : WeilIs A L k (x ^ l) y c') : c = c' := by sorry
