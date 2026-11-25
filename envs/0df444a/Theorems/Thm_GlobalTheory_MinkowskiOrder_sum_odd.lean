-- Prove2me | Theorems.Thm_GlobalTheory_MinkowskiOrder_sum_odd
-- name    : GlobalTheory.MinkowskiOrder.sum_odd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:43.754534+00:00
-- url     : https://prove2.me/theorems/df9269df-7875-53ec-a85e-f93c0b139c53
-- title:
--   Minkowski Order: sum odd
-- statement:
--   The Minkowski Order construction uses the sum odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L88-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L88-L141

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

theorem GlobalTheory.MinkowskiOrder.sum_odd (p l : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (hl : l.Prime) (hpl : p < l)
    (h : ∀ i, p ^ 2 ∣ l ^ i - 1 → p * (p - 1) ∣ i) (n : ℕ) :
    ∑ i ∈ Finset.range n, padicValNat p (l ^ (i + 1) - 1)
      ≤ n / (p - 1) + padicValNat p (n / (p - 1)).factorial := by sorry
