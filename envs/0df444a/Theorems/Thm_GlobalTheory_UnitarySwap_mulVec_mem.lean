-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_mulVec_mem
-- name    : GlobalTheory.UnitarySwap.mulVec_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:45:07.861328+00:00
-- url     : https://prove2.me/theorems/c9a28822-222a-43fb-a198-8cebfea40aa5
-- title:
--   Unitary Swap: mul Vec mem
-- statement:
--   The Unitary Swap construction uses the mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L311-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L311-L314

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ImportsTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnitarySwap
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable {n : ℕ} {σ : L →+* L}

theorem GlobalTheory.UnitarySwap.mulVec_mem {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j, M i j ∈ intL L) {v : Fin n → L}
    (hv : v ∈ intVec L n) : M *ᵥ v ∈ intVec L n := by sorry
