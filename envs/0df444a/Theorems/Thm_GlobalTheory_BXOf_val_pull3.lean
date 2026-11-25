-- Prove2me | Theorems.Thm_GlobalTheory_BXOf_val_pull3
-- name    : GlobalTheory.BXOf.val_pull3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:52:44.82817+00:00
-- url     : https://prove2.me/theorems/82e032fd-d49b-4253-bb8f-1524cdb740f3
-- title:
--   BXOf: val pull3
-- statement:
--   The BXOf construction uses the val pull3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L105-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)
  {T : Over S₀} {z : T.left} {J : (T.left ⟶ (G ⊗ G).left) → P.ι}

theorem GlobalTheory.BXOf.val_pull3 {K : Type} [Fintype K] {φ : K → ((G3 G).left ⟶ (G ⊗ G).left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb P φ ε)) (hJ : Good P z J) {T' : Over S₀} (ρ : T ⟶ T') (x x' y : T' ⟶ G) :
    val (LB.pullGen P φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by sorry
