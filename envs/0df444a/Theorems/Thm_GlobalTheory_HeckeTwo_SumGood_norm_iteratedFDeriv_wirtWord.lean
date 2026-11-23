-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_SumGood_norm_iteratedFDeriv_wirtWord
-- name    : GlobalTheory.HeckeTwo.SumGood.norm_iteratedFDeriv_wirtWord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:59.402249+00:00
-- url     : https://prove2.me/theorems/885453fd-a750-417e-860d-25fc2e0585ae
-- title:
--   Sum Good: norm iterated FDeriv wirt Word
-- statement:
--   The Sum Good construction uses the norm iterated FDeriv wirt Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L95-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsum.lean#L95-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.SumGood
variable {Φ : Type} [Fintype Φ] {ι : Type}

theorem GlobalTheory.HeckeTwo.SumGood.norm_iteratedFDeriv_wirtWord {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : (Φ → ℂ) → ℂ, ContDiffOn ℝ ∞ h U → ∀ k : ℕ, ∀ z ∈ U,
      ‖iteratedFDeriv ℝ k (wirtWord w h) z‖ ≤ C * ‖iteratedFDeriv ℝ (k + w.length) h z‖ := by sorry
