-- Prove2me | Theorems.Thm_GlobalTheory_packetSum_vdm_eq_det
-- name    : GlobalTheory.packetSum_vdm_eq_det
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:54:39.866993+00:00
-- url     : https://prove2.me/theorems/dfc5f41f-1dbe-558c-a4a4-08a22fb026db
-- title:
--   Global Theory: packet Sum vdm eq det
-- statement:
--   The Global Theory construction uses the packet Sum vdm eq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PacketSumSignCastNeZero.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PacketSumSignCastNeZero.lean#L9-L18

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

theorem GlobalTheory.packetSum_vdm_eq_det {r : ℕ} (β : Fin r → ℂ) :
    Formalism.PacketSums.vdm β = (∏ i : Fin r, ∏ _j ∈ Ioi i, (-1 : ℂ)) * (Matrix.vandermonde β).det := by sorry
