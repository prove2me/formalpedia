-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_matrix_mul_apply
-- name    : GlobalTheory.differentiableOn_matrix_mul_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:06.453442+00:00
-- url     : https://prove2.me/theorems/281b640d-e3ba-41be-80f4-7e51781ac145
-- title:
--   Global Theory: differentiable On matrix mul apply
-- statement:
--   The Global Theory construction uses the differentiable On matrix mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L376-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L376-L381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}

theorem GlobalTheory.differentiableOn_matrix_mul_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : Type*} [Fintype n] {M N : E → Matrix n n ℂ} {U : Set E}
    (hM : ∀ i j, DifferentiableOn ℂ (fun x => M x i j) U)
    (hN : ∀ i j, DifferentiableOn ℂ (fun x => N x i j) U) (i j : n) :
    DifferentiableOn ℂ (fun x => (M x * N x) i j) U := by sorry
