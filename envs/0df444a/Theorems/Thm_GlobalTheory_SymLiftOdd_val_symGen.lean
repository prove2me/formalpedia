-- Prove2me | Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
-- name    : GlobalTheory.SymLiftOdd.val_symGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:07.274843+00:00
-- url     : https://prove2.me/theorems/45a2510d-33fc-4740-a7cf-e8f1182906f7
-- title:
--   Sym Lift Odd: val sym Gen
-- statement:
--   The Sym Lift Odd construction uses the val sym Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L130-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SymmetricLiftOddOrderExistsUnique.lean#L130-L145

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

theorem GlobalTheory.SymLiftOdd.val_symGen (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {x : T ⟶ A} (hx : θ.pt = x)
    {y : (T ⊗ A).left} {J} (hJ : Good L y J) (m : T ⊗ A ⟶ A) :
    val (symGen A L k θ nu) (lift (fst T A) m).left y J =
      thetaVal θ y J ((fst T A ≫ x)⁻¹ * m) * negVal nu y J m *
        (thetaVal θ y J m⁻¹ * (negVal nu y J ((fst T A ≫ x)⁻¹ * m))⁻¹) := by sorry
