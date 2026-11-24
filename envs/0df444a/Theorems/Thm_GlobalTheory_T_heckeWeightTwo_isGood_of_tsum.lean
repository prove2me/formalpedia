-- Prove2me | Theorems.Thm_GlobalTheory_T_heckeWeightTwo_isGood_of_tsum
-- name    : GlobalTheory.T.heckeWeightTwo_isGood_of_tsum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:46:30.900001+00:00
-- url     : https://prove2.me/theorems/2e577537-e027-4b77-8bc1-2e065660068d
-- title:
--   T: hecke Weight Two is Good of tsum
-- statement:
--   The T construction uses the hecke Weight Two is Good of tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsumStatement.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoIsGoodOfTsumStatement.lean#L12-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoIsGoodOfTsumStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heckeWeightTwo_isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
  (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
  (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
  (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
  IsGood P := by sorry
