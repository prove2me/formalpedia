-- Prove2me | Theorems.Thm_GlobalTheory_WeilMul_prod_theta
-- name    : GlobalTheory.WeilMul.prod_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:23.589307+00:00
-- url     : https://prove2.me/theorems/7885d02f-82f6-4463-903e-3de29e982d50
-- title:
--   Weil Mul: prod theta
-- statement:
--   The Weil Mul construction uses the prod theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L44-L50

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

theorem GlobalTheory.WeilMul.prod_theta {T T' : Over S} (x : T ⟶ A) (t : T' ⟶ T) (a : T' ⟶ A) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ A.left) → U) :
    ∏ i : Fin 2, h ((lift t a).left ≫ ![(snd T A).left, (translPt A x).left] i) ^ (![k, -k] i) =
      h a.left ^ k * h ((t ≫ x) * a).left ^ (-k) := by sorry
