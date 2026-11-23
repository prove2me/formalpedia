-- Prove2me | Theorems.Thm_GlobalTheory_WeilMul_val_const
-- name    : GlobalTheory.WeilMul.val_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:11.449935+00:00
-- url     : https://prove2.me/theorems/386c1bfe-9b48-461b-aec1-ed51032c9b2d
-- title:
--   Weil Mul: val const
-- statement:
--   The Weil Mul construction uses the val const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L71-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem GlobalTheory.WeilMul.val_const {T T' : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) (t : T' ⟶ overRes V) (a : T' ⟶ A)
    (z : T'.left) (J) :
    val (constGen A L (unitRes V c)) (lift t a).left z J = gm (t ≫ overResι V).left z ⊤ c := by sorry
