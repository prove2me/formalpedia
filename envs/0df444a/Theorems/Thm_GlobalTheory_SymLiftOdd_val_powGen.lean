-- Prove2me | Theorems.Thm_GlobalTheory_SymLiftOdd_val_powGen
-- name    : GlobalTheory.SymLiftOdd.val_powGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:20.691312+00:00
-- url     : https://prove2.me/theorems/5fc4b542-23e3-4d74-871a-01237bc1f8d5
-- title:
--   Sym Lift Odd: val pow Gen
-- statement:
--   The Sym Lift Odd construction uses the val pow Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L166-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L166-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SymLiftOdd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
variable {T : Over S} {k : ℤ}

theorem GlobalTheory.SymLiftOdd.val_powGen (θ : ThetaGrp A L k T) (n : ℕ) {x : T ⟶ A} (hx : θ.pt = x)
    {y : (T ⊗ A).left} {J} (hJ : Good L y J) (m : T ⊗ A ⟶ A) :
    val (powGen A L k θ n) (lift (fst T A) m).left y J =
      ∏ j ∈ Finset.range n, thetaVal θ y J ((fst T A ≫ x) ^ j * m) := by sorry
