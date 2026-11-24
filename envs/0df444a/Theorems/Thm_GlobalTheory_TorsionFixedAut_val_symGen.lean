-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFixedAut_val_symGen
-- name    : GlobalTheory.TorsionFixedAut.val_symGen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:30.39329+00:00
-- url     : https://prove2.me/theorems/bd10fb95-e1aa-4ba3-bb13-d05bcd38ac15
-- title:
--   Torsion Fixed Aut: val sym Gen
-- statement:
--   The Torsion Fixed Aut construction uses the val sym Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L242-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/EqIdOfFixesTorsion.lean#L242-L254

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem GlobalTheory.TorsionFixedAut.val_symGen {k : ℤ} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) : val (symGen A L k θ nu) r z J =
      thetaVal θ.φ
        (r ≫ (translT A θ.pt⁻¹).left) z J *
      negVal nu r z J *
      (thetaVal θ.φ
        (r ≫ (negT A T).left) z J *
      (negVal nu
        (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by sorry
