-- Prove2me | Theorems.Thm_GlobalTheory_SecGrowth_sec_eq_zero
-- name    : GlobalTheory.SecGrowth.sec_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:33.246217+00:00
-- url     : https://prove2.me/theorems/f023364d-25e7-4ac3-9487-8a6396a5c707
-- title:
--   Sec Growth: sec eq zero
-- statement:
--   The Sec Growth construction uses the sec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FiniteOfNotLinearIndependent.lean#L69-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
variable {X : Scheme.{0}}

theorem GlobalTheory.SecGrowth.sec_eq_zero [IsIntegral X] {M : LB X} (σ : LB.Sec M) {k₀ : M.ι} {W : X.Opens} (hW : W ≤ M.U k₀)
    [Nonempty W] (h : rs X hW (σ.f k₀) = 0) (k : M.ι) : σ.f k = 0 := by sorry
