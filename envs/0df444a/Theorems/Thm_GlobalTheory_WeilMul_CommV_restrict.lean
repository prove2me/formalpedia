-- Prove2me | Theorems.Thm_GlobalTheory_WeilMul_CommV_restrict
-- name    : GlobalTheory.WeilMul.CommV.restrict
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:15.080482+00:00
-- url     : https://prove2.me/theorems/6bd5f0d3-489a-4740-86b1-ab278203820e
-- title:
--   Comm V: restrict
-- statement:
--   The Comm V construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L162-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L162-L170

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

theorem GlobalTheory.WeilMul.CommV.restrict (hL : L.IsLB) {T T₀ T₁ : Over S}
    {θx θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c) (f : T₁ ⟶ T) :
    ∃ θx₁ θy₁ : ThetaGrp A L k T₁, θx₁.pt = f ≫ θx.pt ∧ θy₁.pt = f ≫ θy.pt ∧ CommV θx₁ θy₁ (f ≫ g) c := by sorry
