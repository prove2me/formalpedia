-- Prove2me | Theorems.Thm_GlobalTheory_UU_PackageDescent_exists_action
-- name    : GlobalTheory.UU.PackageDescent.exists_action
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:16.057003+00:00
-- url     : https://prove2.me/theorems/651f37a9-5b56-5d3e-8224-3be39e55cbd0
-- title:
--   Package Descent: exists action
-- statement:
--   The Package Descent construction uses the exists action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L137-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsDescendThrough.lean#L137-L157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}

theorem GlobalTheory.UU.PackageDescent.exists_action {L : RigLB G} {c : CubicalStr G L} (s : BiTriv c i) (σ : CubTriv c i) :
    ∃ a : LB.Gen (LB.LinComb L.L (K := Fin 2) ![((fst H G ≫ i) * snd H G).left, (snd H G).left] ![1, -1]), a.IsGen ∧
      ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L.L z J →
        val a (lift t x).left z J = val s.s (lift t x).left z J * val σ.s t.left z J := by sorry
