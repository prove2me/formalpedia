-- Prove2me | Theorems.Thm_GlobalTheory_WeilLocal_local_of_openImmersion
-- name    : GlobalTheory.WeilLocal.local_of_openImmersion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:51.393447+00:00
-- url     : https://prove2.me/theorems/decde9be-93ee-4db7-8420-6d71fc89d6aa
-- title:
--   Weil Local: local of open Immersion
-- statement:
--   The Weil Local construction uses the local of open Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/WeilIsLocalOnBaseOfOpenCover.lean#L68-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/WeilIsLocalOnBaseOfOpenCover.lean#L68-L102

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

theorem GlobalTheory.WeilLocal.local_of_openImmersion (hL : L.IsLB) {T T' : Over S} (j : T' ⟶ T) [IsOpenImmersion j.left]
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ}
    (H : WeilIs A L k (j ≫ x) (j ≫ y) (Units.map j.left.appTop.hom.toMonoidHom c)) (p : T'.left) :
    ∃ V : T.left.Opens, j.left p ∈ V ∧
      (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
      ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
        CommIsOf A L k θx θy (unitRes V c) := by sorry
