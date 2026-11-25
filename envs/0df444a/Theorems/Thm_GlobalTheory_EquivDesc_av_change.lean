-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_av_change
-- name    : GlobalTheory.EquivDesc.av_change
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:08.023905+00:00
-- url     : https://prove2.me/theorems/a2b5a13e-c9a2-5db9-bf14-6a3736b889d4
-- title:
--   Equiv Desc: av change
-- statement:
--   The Equiv Desc construction uses the av change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L139-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L139-L146

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

theorem GlobalTheory.EquivDesc.av_change (ha : a.IsGen) {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left) {k₁ k₂ l₁ l₂ : L.ι}
    (h₁ : ((t ≫ i) * x).left z ∈ L.U k₁) (h₂ : x.left z ∈ L.U k₂)
    (g₁ : ((t ≫ i) * x).left z ∈ L.U l₁) (g₂ : x.left z ∈ L.U l₂) :
    av a t x z k₁ k₂ = gm ((t ≫ i) * x).left z _ (L.g k₁ l₁) * (gm x.left z _ (L.g k₂ l₂))⁻¹ * av a t x z l₁ l₂ := by sorry
