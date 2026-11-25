-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_gapSubset_of_setBound_integral
-- name    : GlobalTheory.CompareIterDegree.gapSubset_of_setBound_integral
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:06.138315+00:00
-- url     : https://prove2.me/theorems/c8510d91-8ca4-4bcf-81d5-a28144900d53
-- title:
--   Compare Iter Degree: gap Subset of set Bound integral
-- statement:
--   The Compare Iter Degree construction uses the gap Subset of set Bound integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L432-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L432-L472

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords

theorem GlobalTheory.CompareIterDegree.gapSubset_of_setBound_integral (h : DegSetBound) (n : ℕ) (μ : Fin n → ℝ) (I : Finset (Fin n))
    (hanti : StrictAnti μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ)) :
    ((∀ J ⊆ I, GapTwo (μ + eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ + eSet I) / fdegHC μ ∧
        fdegHC (μ + eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) ∧
    ((∀ J ⊆ I, GapTwo (μ - eSet J)) →
      (1 / (4 * (n : ℝ) ^ 2)) ^ I.card ≤ fdegHC (μ - eSet I) / fdegHC μ ∧
        fdegHC (μ - eSet I) / fdegHC μ ≤ (Real.exp 1 * n) ^ I.card) := by sorry
