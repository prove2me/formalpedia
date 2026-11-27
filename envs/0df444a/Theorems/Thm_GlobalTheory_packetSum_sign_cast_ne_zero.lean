-- Prove2me | Theorems.Thm_GlobalTheory_packetSum_sign_cast_ne_zero
-- name    : GlobalTheory.packetSum_sign_cast_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:55:07.324342+00:00
-- url     : https://prove2.me/theorems/d33a0ed2-c531-4e3b-a43b-8907db7c620a
-- title:
--   Global Theory: packet Sum sign cast ne zero
-- statement:
--   The Global Theory construction uses the packet Sum sign cast ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PacketSumSignCastNeZero.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PacketSumSignCastNeZero.lean#L28-L30

import Mathlib
import Definitions.Def_Formalism_JacquetSubsetSums_JacquetSubsetSum
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PacketSumSignCastNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.packetSum_sign_cast_ne_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by sorry
