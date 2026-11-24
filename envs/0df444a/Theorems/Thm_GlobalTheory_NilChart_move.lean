-- Prove2me | Theorems.Thm_GlobalTheory_NilChart_move
-- name    : GlobalTheory.NilChart.move
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:26:01.983213+00:00
-- url     : https://prove2.me/theorems/8ba84cbc-cb67-4559-abae-6574a4f0ddfc
-- title:
--   Nil Chart: move
-- statement:
--   The Nil Chart construction uses the move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueCoord.lean#L41-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueCoord.lean#L41-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueCoord
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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilChart
open SqZero
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) {d : ℕ}
  {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G}
  (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
  (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
  (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
include hG hv hx₁ hx₂ hx₃

theorem GlobalTheory.NilChart.move {I J : Ideal B} (hJ : J * I = ⊥) (hle : J ≤ I) {m : ℕ} (ψ ψ' : JetR R (Fin d) m →ₐ[R] B)
    (hψ : ∀ j, ψ (zR m j) ∈ I) (c : Fin d → B) (hcJ : ∀ j, c j ∈ J) (hc : ∀ j, c j * c j = 0)
    (h : ∀ j, ψ' (zR m j) = ψ (zR m j) + c j) : spMap ψ' ≫ x m = lieExp v c hc * (spMap ψ ≫ x m) := by sorry
