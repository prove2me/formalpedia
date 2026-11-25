-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_exists_odd
-- name    : GlobalTheory.CubeLift.exists_odd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:15:44.879346+00:00
-- url     : https://prove2.me/theorems/31361dbd-1c00-4ab9-bbce-086965b95c27
-- title:
--   Cube Lift: exists odd
-- statement:
--   The Cube Lift construction uses the exists odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean#L111-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean#L111-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenLiftOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsEvenCubicalTrivialisationLiftNilpotent
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (bcMap)
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] {i : H ⟶ G}
variable [IsCommMonObj G] [GrpObj H] [IsMonHom i]

theorem GlobalTheory.CubeLift.exists_odd (P : CP G)
    (t : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (ht : t.IsGen) :
    ∃ E : Γ(H.left, ⊤)ˣ, ∀ (T : Over S) (x : T ⟶ H) (z : T.left) (J), Good P.L.L z J →
      val t (x⁻¹).left z J = gm x.left z ⊤ E * (val P.sym (x ≫ i).left z J * val t x.left z J) := by sorry
