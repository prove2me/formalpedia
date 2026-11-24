-- Prove2me | Theorems.Thm_GlobalTheory_CosetAvg_avg_of_invariant
-- name    : GlobalTheory.CosetAvg.avg_of_invariant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:02.611449+00:00
-- url     : https://prove2.me/theorems/51876945-eb75-4dc1-b9e4-12b339762725
-- title:
--   Coset Avg: avg of invariant
-- statement:
--   The Coset Avg construction uses the avg of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTranslatesEqDoubleCosetAverage.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumTranslatesEqDoubleCosetAverage.lean#L25-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumTranslatesEqDoubleCosetAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.CosetAvg
open MulAction

theorem GlobalTheory.CosetAvg.avg_of_invariant {H X M ι : Type*} [Group H] [Fintype H] [MulAction H X]
    [AddCommGroup M] [Module ℂ M] (s : Finset ι) (y : ι → X) [∀ i, Fintype (orbit H (y i))]
    (F : ι → X → M) (hinv : ∀ h : H, ∑ i ∈ s, F i (h • y i) = ∑ i ∈ s, F i (y i)) :
    ∑ i ∈ s, F i (y i) =
      ∑ i ∈ s, ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by sorry
