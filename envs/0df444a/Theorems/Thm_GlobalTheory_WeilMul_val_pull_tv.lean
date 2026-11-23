-- Prove2me | Theorems.Thm_GlobalTheory_WeilMul_val_pull_tv
-- name    : GlobalTheory.WeilMul.val_pull_tv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:02.784276+00:00
-- url     : https://prove2.me/theorems/ebd2b52a-a1cf-4a6d-b209-a3b576118268
-- title:
--   Weil Mul: val pull tv
-- statement:
--   The Weil Mul construction uses the val pull tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L59-L64

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

theorem GlobalTheory.WeilMul.val_pull_tv {T T₁ T' : Over S} (θ : ThetaGrp A L k T) (t : T₁ ⟶ T) (a : T₁ ⟶ A) (ρ : T' ⟶ T₁)
    {z : T'.left} {J} (hJ : Good L z J) :
    val (LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (lift t a).left)
      ρ.left z J = tv θ (ρ ≫ t) (ρ ≫ a) z J := by sorry
