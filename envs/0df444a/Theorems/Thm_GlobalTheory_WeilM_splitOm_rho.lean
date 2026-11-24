-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_splitOm_rho
-- name    : GlobalTheory.WeilM.splitOm_rho
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:50.354198+00:00
-- url     : https://prove2.me/theorems/7278bd7e-8da5-4f53-9af2-f740fdfb4eb0
-- title:
--   Weil M: split Om rho
-- statement:
--   The Weil M construction uses the split Om rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L199-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L199-L243

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

theorem GlobalTheory.WeilM.splitOm_rho [Invertible (2 : R)] (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) {JA : Matrix α α (R × R)}
    {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA) (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (ψ : AddChar R ℂ)
    (h : UG (swapA R) JB) (w : Matrix α β (R × R)) (φ : (κ → R) → ℂ) :
    splitOm m χ JB σ h ((splitDarboux hA hB σ).rho ψ w φ) =
      (splitDarboux hA hB σ).rho ψ (actB (swapA R) h w) (splitOm m χ JB σ h φ) := by sorry
