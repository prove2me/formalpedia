-- Prove2me | Theorems.Thm_GlobalTheory_WeilLocal_commIsOf_of_retract
-- name    : GlobalTheory.WeilLocal.commIsOf_of_retract
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:50.493894+00:00
-- url     : https://prove2.me/theorems/95436180-a446-4c60-8ab3-e8c2603ab033
-- title:
--   Weil Local: comm Is Of of retract
-- statement:
--   The Weil Local construction uses the comm Is Of of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/WeilIsLocalOnBaseOfOpenCover.lean#L28-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/WeilIsLocalOnBaseOfOpenCover.lean#L28-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsIffOfIsGrpPullbackComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsLocalOnBaseOfOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.WeilLocal
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem GlobalTheory.WeilLocal.commIsOf_of_retract (hL : L.IsLB) {T T' : Over S} (g : T' ⟶ T) (h : T ⟶ T') (w : g ≫ h = 𝟙 T')
    {c : Γ(T.left, ⊤)ˣ} (θx' θy' : ThetaGrp A L k T')
    (H : ∀ θx θy : ThetaGrp A L k T, θx.pt = h ≫ θx'.pt → θy.pt = h ≫ θy'.pt → CommIsOf A L k θx θy c) :
    CommIsOf A L k θx' θy' (Units.map g.left.appTop.hom.toMonoidHom c) := by sorry
