-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isSplitting_splitOm
-- name    : GlobalTheory.WeilM.isSplitting_splitOm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:55:05.234973+00:00
-- url     : https://prove2.me/theorems/0e81bb82-17ee-4bcc-a72e-2831a0f6e104
-- title:
--   Weil M: is Splitting split Om
-- statement:
--   The Weil M construction uses the is Splitting split Om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L271-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L271-L277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem GlobalTheory.WeilM.isSplitting_splitOm [Invertible (2 : R)] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) {JA : Matrix α α (R × R)}
    {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA) (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (ψ : AddChar R ℂ) :
    IsSplitting (sbClass R) ψ (splitDarboux hA hB σ) (actB (swapA R)) (splitOm m χ JB σ) := by sorry
