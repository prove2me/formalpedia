-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_entries_mem
-- name    : GlobalTheory.UnitarySwap.entries_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:47:50.665875+00:00
-- url     : https://prove2.me/theorems/6d8e5f38-ced4-4013-a479-0d16930bdead
-- title:
--   Unitary Swap: entries mem
-- statement:
--   The Unitary Swap construction uses the entries mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L322-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L322-L324

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

theorem GlobalTheory.UnitarySwap.entries_mem {M : Matrix (Fin n) (Fin n) L} (hM : ∀ v ∈ intVec L n, M *ᵥ v ∈ intVec L n)
    (i j : Fin n) : M i j ∈ intL L := by sorry
