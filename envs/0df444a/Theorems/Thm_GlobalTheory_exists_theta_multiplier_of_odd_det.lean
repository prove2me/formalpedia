-- Prove2me | Theorems.Thm_GlobalTheory_exists_theta_multiplier_of_odd_det
-- name    : GlobalTheory.exists_theta_multiplier_of_odd_det
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:50.586309+00:00
-- url     : https://prove2.me/theorems/51552d6f-f310-4bd1-8355-b49d543fae95
-- title:
--   Global Theory: exists theta multiplier of odd det
-- statement:
--   The Global Theory construction uses the exists theta multiplier of odd det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L430-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L430-L446

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

theorem GlobalTheory.exists_theta_multiplier_of_odd_det (hγ : γ ∈ symplecticGroup (Fin g) ℤ)
    (hodd : Odd γ.toBlocks₂₂.det)
    (hb : ∀ μ, Even (μ ⬝ᵥ (γ.toBlocks₂₂ᵀ * γ.toBlocks₁₂) *ᵥ μ))
    (hc : ∀ μ, Even (μ ⬝ᵥ (γ.toBlocks₁₁ᵀ * γ.toBlocks₂₁) *ᵥ μ)) :
    ∃ l : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g l ∧ ∀ τ ∈ SiegelH (Fin g),
      (∀ z, theta 0 0 (zAct γ τ z) (spAct γ τ) * eC (-expArg γ τ z / 2) = l τ * theta 0 0 z τ) ∧
      l τ ^ 2 = (ZMod.χ₄ (γ.toBlocks₂₂.det : ZMod 4) : ℤ) * (jAut γ τ).det := by sorry
