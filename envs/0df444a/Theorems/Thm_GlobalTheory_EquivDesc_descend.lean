-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_descend
-- name    : GlobalTheory.EquivDesc.descend
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:16.811804+00:00
-- url     : https://prove2.me/theorems/d3004a08-0e5f-4be8-8447-9e15cd5a2d15
-- title:
--   Equiv Desc: descend
-- statement:
--   The Equiv Desc construction uses the descend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L339-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L339-L376

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
variable {G B H : Over S} [GrpObj G] [GrpObj B] [GrpObj H] {q : G ⟶ B} {i : H ⟶ G} [IsMonHom q] [IsMonHom i]
  {L : LB G.left} {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}

theorem GlobalTheory.EquivDesc.descend [Flat q.left] [Surjective q.left] [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q η[B])
    (hL : L.IsLB) (h : ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ ∃ e, InvGen q a V e) :
    ∃ (M : LB B.left) (w : LB.Iso L (M.pull q.left)), M.IsLB ∧ w.IsGen ∧
      ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J) (j : M.ι), Good L z J → q.left (x.left z) ∈ M.U j →
        gw w ((t ≫ i) * x).left z j (J ((t ≫ i) * x).left) * val a (lift t x).left z J = gw w x.left z j (J x.left) := by sorry
