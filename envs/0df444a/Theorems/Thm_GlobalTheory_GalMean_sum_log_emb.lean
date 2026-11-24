-- Prove2me | Theorems.Thm_GlobalTheory_GalMean_sum_log_emb
-- name    : GlobalTheory.GalMean.sum_log_emb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:40.629114+00:00
-- url     : https://prove2.me/theorems/c562e8a9-971a-49ba-bd55-d3967541a5eb
-- title:
--   Gal Mean: sum log emb
-- statement:
--   The Gal Mean construction uses the sum log emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L35-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L35-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeanLogNormConjugatesOverIdealClasses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.GalMean
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open IntermediateField

theorem GlobalTheory.GalMean.sum_log_emb (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [NumberField L] (β : ℂ) (hβ : β ∈ L)
    (h0 : β ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ Module.finrank ℚ L = m * (minpoly ℚ β).natDegree ∧
      ∑ τ : L →+* ℂ, Real.log ‖τ ⟨β, hβ⟩‖ = m * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| := by sorry
