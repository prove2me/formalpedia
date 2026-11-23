-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_det_siegel
-- name    : GlobalTheory.WeilM.det_siegel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:23.801815+00:00
-- url     : https://prove2.me/theorems/ec35d727-3aed-4ac4-a7cd-ac8b3b56ad44
-- title:
--   Weil M: det siegel
-- statement:
--   The Weil M construction uses the det siegel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L308-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L308-L373

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

theorem GlobalTheory.WeilM.det_siegel {JB : Matrix β β (R × R)} (hB : IsHerm (swapA R) JB) (p : UG (swapA R) (dbl JB))
    (t : Matrix β β (R × R))
    (h : ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * (diagCols β : Matrix (β ⊕ β) β (R × R)) =
      (diagCols β : Matrix (β ⊕ β) β (R × R)) * t) :
    (ugFst _ p).val * (diagCols β : Matrix (β ⊕ β) β R) = (diagCols β : Matrix (β ⊕ β) β R) * cmp₁ t ∧
      (ugFst _ p).val.det * (cmp₂ t).det = (cmp₁ t).det := by sorry
