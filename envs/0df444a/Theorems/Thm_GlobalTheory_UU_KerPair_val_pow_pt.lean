-- Prove2me | Theorems.Thm_GlobalTheory_UU_KerPair_val_pow_pt
-- name    : GlobalTheory.UU.KerPair.val_pow_pt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:09:07.360217+00:00
-- url     : https://prove2.me/theorems/354356e3-9c96-41b9-83c5-0a627937ad29
-- title:
--   Ker Pair: val pow pt
-- statement:
--   The Ker Pair construction uses the val pow pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubWeilOfGen.lean#L117-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubWeilOfGen.lean#L117-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOfGen
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.KerPair
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}

theorem GlobalTheory.UU.KerPair.val_pow_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) {N : ℕ} (hx : x ^ N = 1) (b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    cubN (cubV c z J) N 1 x b * val u (lift (𝟙 T) b).left z J ^ N = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := by sorry
