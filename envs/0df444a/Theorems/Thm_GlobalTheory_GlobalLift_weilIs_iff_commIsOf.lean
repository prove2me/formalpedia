-- Prove2me | Theorems.Thm_GlobalTheory_GlobalLift_weilIs_iff_commIsOf
-- name    : GlobalTheory.GlobalLift.weilIs_iff_commIsOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:25.019389+00:00
-- url     : https://prove2.me/theorems/618b1463-b71b-4bef-9024-c0bcfd88374f
-- title:
--   Global Lift: weil Is iff comm Is Of
-- statement:
--   The Global Lift construction uses the weil Is iff comm Is Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsIffCommIsOfAndLiftSubsingleton.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsIffCommIsOfAndLiftSubsingleton.lean#L27-L32

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

theorem GlobalTheory.GlobalLift.weilIs_iff_commIsOf (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {T : Over S}
    (θx θy : ThetaGrp A L k T) (c : Γ(T.left, ⊤)ˣ) : WeilIs A L k θx.pt θy.pt c ↔ CommIsOf A L k θx θy c := by sorry
