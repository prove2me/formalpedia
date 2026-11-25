-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_av_mul
-- name    : GlobalTheory.EquivDesc.av_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:44.880835+00:00
-- url     : https://prove2.me/theorems/8688d403-f39f-4b45-aa44-272f93a2c25d
-- title:
--   Equiv Desc: av mul
-- statement:
--   The Equiv Desc construction uses the av mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L152-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L152-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
variable {G H : Over S} [GrpObj G] [GrpObj H] {i : H ⟶ G} {L : LB G.left}
variable {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}

theorem GlobalTheory.EquivDesc.av_mul [IsMonHom i] (hL : L.IsLB) (ha : a.IsGen) (hc : IsAct a) {T : Over S} (t t' : T ⟶ H) (x : T ⟶ G)
    (z : T.left) {k₁ k₂ k₃ : L.ι} (h₁ : (((t * t') ≫ i) * x).left z ∈ L.U k₁) (h₂ : ((t' ≫ i) * x).left z ∈ L.U k₂)
    (h₃ : x.left z ∈ L.U k₃) :
    av a (t * t') x z k₁ k₃ = av a t ((t' ≫ i) * x) z k₁ k₂ * av a t' x z k₂ k₃ := by sorry
