-- Prove2me | Theorems.Thm_GlobalTheory_NilChart_mk_comp_eq
-- name    : GlobalTheory.NilChart.mk_comp_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:26:31.468188+00:00
-- url     : https://prove2.me/theorems/d001eb37-4a70-4e0a-bf7c-d0ae152a4dbe
-- title:
--   Nil Chart: mk comp eq
-- statement:
--   The Nil Chart construction uses the mk comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueCoord.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueCoord.lean#L27-L31

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

theorem GlobalTheory.NilChart.mk_comp_eq {κ : Type} {m : ℕ} {I : Ideal B} (ψ : JetR R κ m →ₐ[R] B) (h : ∀ j, ψ (zR m j) ∈ I) :
    (Ideal.Quotient.mkₐ R I).comp ψ = (Algebra.ofId R _).comp (jetAug R κ m) := by sorry
