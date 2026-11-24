-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCoord_isActOf_self
-- name    : GlobalTheory.ThetaCoord.isActOf_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:17:26.590801+00:00
-- url     : https://prove2.me/theorems/8c3ef22d-16c0-4178-b2f7-affa59e01a66
-- title:
--   Theta Coord: is Act Of self
-- statement:
--   The Theta Coord construction uses the is Act Of self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L425-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverOfSubsingleton.lean#L425-L443

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

theorem GlobalTheory.ThetaCoord.isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {m q : ℕ} (hq : Odd q)
    {ν : LB.Gen (negLB A L b T)} (hν : ν.IsGen)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L b T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a b α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by sorry
