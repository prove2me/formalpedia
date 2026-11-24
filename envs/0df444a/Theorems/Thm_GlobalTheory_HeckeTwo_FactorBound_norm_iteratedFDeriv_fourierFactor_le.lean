-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_FactorBound_norm_iteratedFDeriv_fourierFactor_le
-- name    : GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:06:03.202651+00:00
-- url     : https://prove2.me/theorems/7fcb77c9-0455-4654-975a-05c4d09322c0
-- title:
--   Factor Bound: norm iterated FDeriv fourier Factor le
-- statement:
--   The Factor Bound construction uses the norm iterated FDeriv fourier Factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivHeckeFourierFactorLe.lean#L104-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivHeckeFourierFactorLe.lean#L104-L193

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivHeckeFourierFactorLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.FactorBound

theorem GlobalTheory.HeckeTwo.FactorBound.norm_iteratedFDeriv_fourierFactor_le :
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ j : ℕ, ∃ s : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν y : ℝ, ν ≠ 0 → y ≠ 0 →
      ‖iteratedDeriv j (hTrans σ ν) y‖ ≤ C * (|y| + |y|⁻¹) ^ s / (1 + |ν * y|) ^ N) →
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ c c' : ℝ, 0 < c → ∀ k : ℕ, ∃ m : ℕ, ∀ N : ℕ, ∃ C : ℝ,
    ∀ σ ∈ K, ∀ ν β : ℝ, ν ≠ 0 → β ≠ 0 → ∀ w : ℂ, c ≤ w.im → w.im ≤ c' →
      ‖iteratedFDeriv ℝ k (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * ((ν * β * w.re : ℝ) : ℂ)) *
          hTrans σ ν (β * w.im)) w‖ ≤ C * (|β| + |β|⁻¹) ^ m / (1 + |ν * β|) ^ N := by sorry
