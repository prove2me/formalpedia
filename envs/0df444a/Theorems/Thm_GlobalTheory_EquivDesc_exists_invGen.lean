-- Prove2me | Theorems.Thm_GlobalTheory_EquivDesc_exists_invGen
-- name    : GlobalTheory.EquivDesc.exists_invGen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:36:35.012846+00:00
-- url     : https://prove2.me/theorems/0b28afb8-8474-48a9-9268-2f2f6e30dd93
-- title:
--   Equiv Desc: exists inv Gen
-- statement:
--   The Equiv Desc construction uses the exists inv Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L197-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L197-L298

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

theorem GlobalTheory.EquivDesc.exists_invGen [Flat q.left] [Surjective q.left] [QuasiCompact q.left] (hk : IsPullback i (toUnit _) q η[B])
    (hL : L.IsLB) (ha : a.IsGen) (hc : IsAct a) (V₀ : B.left.Opens) (τ : opn (q.left ⁻¹ᵁ V₀) ⟶ H)
    (hτ : ∀ (Z : Over S) (t : Z ⟶ H) (g g' : Z ⟶ opn (q.left ⁻¹ᵁ V₀)),
      g' ≫ opnι _ = (t ≫ i) * (g ≫ opnι _) → g' ≫ τ = t * (g ≫ τ)) (b : B.left) (hb : b ∈ V₀) :
    ∃ V : B.left.Opens, b ∈ V ∧ ∃ e, InvGen q a V e := by sorry
