-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_exists_defect
-- name    : GlobalTheory.CubeLift.exists_defect
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:17:07.315083+00:00
-- url     : https://prove2.me/theorems/94e35d00-7b29-43fd-b367-1a5763544987
-- title:
--   Cube Lift: exists defect
-- statement:
--   The Cube Lift construction uses the exists defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean#L72-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsEvenCubicalTrivialisationLiftNilpotent.lean#L72-L109

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

theorem GlobalTheory.CubeLift.exists_defect {L : RigLB G} (c : CubicalStr G L)
    (t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (ht : t.IsGen)
    {V : Over S} (a b d : V ⟶ H) : ∃ D : Γ(V.left, ⊤)ˣ, ∀ (T : Over S) (ρ : T ⟶ V) (z : T.left) (J), Good L.L z J →
      val t ((ρ ≫ a) * (ρ ≫ b) * (ρ ≫ d)).left z J * val t (ρ ≫ a).left z J * val t (ρ ≫ b).left z J *
        val t (ρ ≫ d).left z J = gm ρ.left z ⊤ D * (cubV c z J ((ρ ≫ a) ≫ i) ((ρ ≫ b) ≫ i) ((ρ ≫ d) ≫ i) *
          val t ((ρ ≫ a) * (ρ ≫ b)).left z J * val t ((ρ ≫ a) * (ρ ≫ d)).left z J *
          val t ((ρ ≫ b) * (ρ ≫ d)).left z J) := by sorry
