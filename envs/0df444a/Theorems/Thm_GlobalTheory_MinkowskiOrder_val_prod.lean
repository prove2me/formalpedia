-- Prove2me | Theorems.Thm_GlobalTheory_MinkowskiOrder_val_prod
-- name    : GlobalTheory.MinkowskiOrder.val_prod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:49.586944+00:00
-- url     : https://prove2.me/theorems/93f8b539-f223-5950-a384-e25b80bd0e78
-- title:
--   Minkowski Order: val prod
-- statement:
--   The Minkowski Order construction uses the val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L49-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L49-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.MinkowskiOrder

theorem GlobalTheory.MinkowskiOrder.val_prod (n p l : ℕ) (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) :
    (∏ i : Fin n, (l ^ n - l ^ (i : ℕ))).factorization p
      = ∑ i ∈ Finset.range n, padicValNat p (l ^ (i + 1) - 1) := by sorry
