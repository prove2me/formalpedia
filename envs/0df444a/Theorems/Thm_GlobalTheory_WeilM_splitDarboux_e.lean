-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_splitDarboux_e
-- name    : GlobalTheory.WeilM.splitDarboux_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:48.673395+00:00
-- url     : https://prove2.me/theorems/8649c107-ca17-4285-a9df-1d6d2b08e409
-- title:
--   Weil M: split Darboux e
-- statement:
--   The Weil M construction uses the split Darboux e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L153-L155

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

theorem GlobalTheory.WeilM.splitDarboux_e {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (x : Matrix α β (R × R)) :
    (splitDarboux hA hB σ).e x = (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ)) := by sorry
