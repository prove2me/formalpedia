-- Prove2me | Theorems.Thm_GlobalTheory_GlobalLift_val_powGen
-- name    : GlobalTheory.GlobalLift.val_powGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:38.170057+00:00
-- url     : https://prove2.me/theorems/c8c1bee6-1ffa-4911-971c-fc1651b5c8ca
-- title:
--   Global Lift: val pow Gen
-- statement:
--   The Global Lift construction uses the val pow Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsIffCommIsOfAndLiftSubsingleton.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsIffCommIsOfAndLiftSubsingleton.lean#L34-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GlobalLift
open CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem GlobalTheory.GlobalLift.val_powGen {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J}
    (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ i : Fin n, tval θ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J := by sorry
