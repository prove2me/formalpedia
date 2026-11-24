-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCoord_isValueAt_of_sv
-- name    : GlobalTheory.ThetaCoord.isValueAt_of_sv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:17:15.019815+00:00
-- url     : https://prove2.me/theorems/2861528d-49e0-4095-a885-e6f62611f567
-- title:
--   Theta Coord: is Value At of sv
-- statement:
--   The Theta Coord construction uses the is Value At of sv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L303-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L303-L314

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}

theorem GlobalTheory.ThetaCoord.isValueAt_of_sv (hL : L.IsLB) {s : LB.Sec (LPow A L k T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))} (hτ : τ.IsGen)
    {v : Γ(T.left, ⊤)} (H : ∀ (z : T.left) (J), Good L z J →
      sv A s (lift (𝟙 T) w).left z J = gs (𝟙 T.left) z ⊤ v * (val τ (𝟙 T.left) z J).val) :
    IsValueAt A L k s w τ v := by sorry
