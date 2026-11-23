-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_flat_fromCols
-- name    : GlobalTheory.WeilM.flat_fromCols
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:26.373398+00:00
-- url     : https://prove2.me/theorems/3fe07bae-3369-4762-9934-38bbab00470f
-- title:
--   Weil M: flat from Cols
-- statement:
--   The Weil M construction uses the flat from Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L291-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSplittingSplitOm.lean#L291-L294

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
omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

theorem GlobalTheory.WeilM.flat_fromCols (σ : κ ≃ α × β) (X Y : Matrix α β R) :
    flat (dblNum σ) (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := by sorry
