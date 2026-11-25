-- Prove2me | Theorems.Thm_GlobalTheory_ConvOfProd_exists_sub_sum
-- name    : GlobalTheory.ConvOfProd.exists_sub_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:13.922785+00:00
-- url     : https://prove2.me/theorems/1242088b-2380-480f-8ee8-66e0980c473e
-- title:
--   Conv Of Prod: exists sub sum
-- statement:
--   The Conv Of Prod construction uses the exists sub sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSubSum.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSubSum.lean#L35-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfSumMulCoord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsProdB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSubSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.ConvOfProd

theorem GlobalTheory.ConvOfProd.exists_sub_sum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Ix : Type}
    (S : LB.Sec (LB.LinComb L φ ε)) (p : Ix → LB.Sec (LB.LinComb L φ ε)) (s : Finset Ix) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval S r z J - ∑ i ∈ s, sval (p i) r z J := by sorry
