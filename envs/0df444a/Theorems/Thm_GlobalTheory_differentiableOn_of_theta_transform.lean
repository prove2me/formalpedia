-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_of_theta_transform
-- name    : GlobalTheory.differentiableOn_of_theta_transform
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:15.807006+00:00
-- url     : https://prove2.me/theorems/5d6935d1-06d7-4c66-aa62-1752102153c9
-- title:
--   Global Theory: differentiable On of theta transform
-- statement:
--   The Global Theory construction uses the differentiable On of theta transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L383-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L383-L419

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

theorem GlobalTheory.differentiableOn_of_theta_transform (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    {l : Matrix (Fin g) (Fin g) ℂ → ℂ} (hl : ∀ τ ∈ SiegelH (Fin g), ∀ z,
      theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : E → Matrix (Fin g) (Fin g) ℂ}
    {U : Set E} (hT : ∀ x ∈ U, T x ∈ SiegelH (Fin g))
    (h1 : ∀ i j, DifferentiableOn ℂ (fun x => T x i j) U) :
    DifferentiableOn ℂ (fun x => l (T x)) U := by sorry
