-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isDblCoord_split
-- name    : GlobalTheory.WeilM.isDblCoord_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:46.502048+00:00
-- url     : https://prove2.me/theorems/12c0a4e1-1a18-486c-8301-53d0464cb751
-- title:
--   Weil M: is Dbl Coord split
-- statement:
--   The Weil M construction uses the is Dbl Coord split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L296-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L296-L306

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

theorem GlobalTheory.WeilM.isDblCoord_split {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) :
    IsDblCoord (swapA R) (1, -1) JA JB (splitDarboux hA hB σ) (splitDarboux hA hB.dbl (dblNum σ)) := by sorry
