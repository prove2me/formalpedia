-- Prove2me | Theorems.Thm_GlobalTheory_MinkowskiOrder_card_dvd_prod
-- name    : GlobalTheory.MinkowskiOrder.card_dvd_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:14:36.914933+00:00
-- url     : https://prove2.me/theorems/d88807d1-3d17-56aa-a73d-35d96044631b
-- title:
--   Minkowski Order: card dvd prod
-- statement:
--   The Minkowski Order construction uses the card dvd prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L8-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/CardFiniteSubgroupGLIntDvd.lean#L8-L47

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

theorem GlobalTheory.MinkowskiOrder.card_dvd_prod (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)) [Finite G] (l : ℕ) (hl : l.Prime)
    (h3 : 3 ≤ l) : Nat.card G ∣ ∏ i : Fin n, (l ^ n - l ^ (i : ℕ)) := by sorry
