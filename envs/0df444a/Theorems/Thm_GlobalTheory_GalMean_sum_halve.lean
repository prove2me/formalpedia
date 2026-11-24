-- Prove2me | Theorems.Thm_GlobalTheory_GalMean_sum_halve
-- name    : GlobalTheory.GalMean.sum_halve
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:14:03.508812+00:00
-- url     : https://prove2.me/theorems/734df748-c670-4a24-9475-2d69cbfdc135
-- title:
--   Gal Mean: sum halve
-- statement:
--   The Gal Mean construction uses the sum halve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L80-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeanLogNormConjugatesOverIdealClasses.lean#L80-L110

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
open Classical

theorem GlobalTheory.GalMean.sum_halve {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (hK2 : Module.finrank ℚ K = 2)
    (hc : (starRingEnd ℂ).comp φK ≠ φK) (L : IntermediateField ℚ ℂ) [NumberField L] (hK : ∀ x : K, φK x ∈ L)
    (f : (L →+* ℂ) → ℝ) (hf : ∀ τ, f ((starRingEnd ℂ).comp τ) = f τ) :
    ∑ τ : L →+* ℂ, f τ =
      2 * ∑ τ ∈ Finset.univ.filter (fun τ : L →+* ℂ => ∀ x : K, τ ⟨φK x, hK x⟩ = φK x), f τ := by sorry
