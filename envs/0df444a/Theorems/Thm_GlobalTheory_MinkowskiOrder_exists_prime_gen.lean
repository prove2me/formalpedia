-- Prove2me | Theorems.Thm_GlobalTheory_MinkowskiOrder_exists_prime_gen
-- name    : GlobalTheory.MinkowskiOrder.exists_prime_gen
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:26:44.584346+00:00
-- url     : https://prove2.me/theorems/36b7c0ab-0e3f-475b-a67b-8ad49b237d48
-- title:
--   Minkowski Order: exists prime gen
-- statement:
--   The Minkowski Order construction uses the exists prime gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L70-L86

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

theorem GlobalTheory.MinkowskiOrder.exists_prime_gen (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ l : ℕ, l.Prime ∧ p < l ∧ ∀ i, p ^ 2 ∣ l ^ i - 1 → p * (p - 1) ∣ i := by sorry
