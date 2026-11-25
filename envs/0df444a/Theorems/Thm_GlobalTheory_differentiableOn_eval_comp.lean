-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_eval_comp
-- name    : GlobalTheory.differentiableOn_eval_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:16.386961+00:00
-- url     : https://prove2.me/theorems/959f3007-7e58-4af1-b521-c8882972dfee
-- title:
--   Global Theory: differentiable On eval comp
-- statement:
--   The Global Theory construction uses the differentiable On eval comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsProjectiveModelPolarisedTorusTheta.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsProjectiveModelPolarisedTorusTheta.lean#L90-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsProjectiveModelPolarisedTorusTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.differentiableOn_eval_comp {σ E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : σ → E → ℂ) (S : Set E)
    (hu : ∀ c, DifferentiableOn ℂ (u c) S) (F : MvPolynomial σ ℂ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval (fun c => u c z) F) S := by sorry
