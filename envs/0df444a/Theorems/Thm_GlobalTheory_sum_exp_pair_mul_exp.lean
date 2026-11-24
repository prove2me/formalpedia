-- Prove2me | Theorems.Thm_GlobalTheory_sum_exp_pair_mul_exp
-- name    : GlobalTheory.sum_exp_pair_mul_exp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:31.401327+00:00
-- url     : https://prove2.me/theorems/ce892e3a-fa22-4bb3-a6ed-87bd24a58914
-- title:
--   Global Theory: sum exp pair mul exp
-- statement:
--   The Global Theory construction uses the sum exp pair mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L100-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FromBlocksMapIntCastMemSymplecticGroup.lean#L100-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_IsSiegel_mk

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b c d : Matrix ι ι ℤ}

theorem GlobalTheory.sum_exp_pair_mul_exp (h : fromBlocks a b c d ∈ symplecticGroup ι ℤ) (hd : d.det ≠ 0)
    (hb : ∀ μ, Even (μ ⬝ᵥ (dᵀ * b) *ᵥ μ)) (hc : ∀ μ, Even (μ ⬝ᵥ (aᵀ * c) *ᵥ μ))
    {κ : Type*} [Fintype κ] (r : κ → ι → ℤ)
    (hr : Function.Bijective fun k =>
      (Submodule.Quotient.mk (r k) : (ι → ℤ) ⧸ LinearMap.range d.mulVecLin)) (m : ι → ℤ) :
    ∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ))) *
      cexp (2 * π * I * ((fun i => (m i : ℂ)) ⬝ᵥ
        (d.map ((↑) : ℤ → ℂ))⁻¹ *ᵥ fun i => (r k i : ℂ))) =
    (∑ k, cexp (π * I * ((fun i => (r k i : ℂ)) ⬝ᵥ
        (b.map ((↑) : ℤ → ℂ) * (d.map ((↑) : ℤ → ℂ))⁻¹) *ᵥ fun i => (r k i : ℂ)))) *
      cexp (π * I * ((fun i => (m i : ℂ)) ⬝ᵥ
        ((d.map ((↑) : ℤ → ℂ))⁻¹ * c.map ((↑) : ℤ → ℂ)) *ᵥ fun i => (m i : ℂ))) := by sorry
