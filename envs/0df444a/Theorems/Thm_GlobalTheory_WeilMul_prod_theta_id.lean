-- Prove2me | Theorems.Thm_GlobalTheory_WeilMul_prod_theta_id
-- name    : GlobalTheory.WeilMul.prod_theta_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:38.534644+00:00
-- url     : https://prove2.me/theorems/5255dbb0-7e46-4a12-b7cb-d8172c5709b0
-- title:
--   Weil Mul: prod theta id
-- statement:
--   The Weil Mul construction uses the prod theta id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L52-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L52-L57

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

theorem GlobalTheory.WeilMul.prod_theta_id {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U]
    (h : ((T ⊗ A).left ⟶ A.left) → U) :
    ∏ i : Fin 2, h (![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h (snd T A).left ^ k * h ((fst T A ≫ x) * snd T A).left ^ (-k) := by sorry
