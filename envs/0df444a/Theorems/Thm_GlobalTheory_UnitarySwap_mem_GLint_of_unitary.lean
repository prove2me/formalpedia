-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_mem_GLint_of_unitary
-- name    : GlobalTheory.UnitarySwap.mem_GLint_of_unitary
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:45:49.558844+00:00
-- url     : https://prove2.me/theorems/b58f8688-2808-4b40-93ad-482b25c342d6
-- title:
--   Unitary Swap: mem GLint of unitary
-- statement:
--   The Unitary Swap construction uses the mem GLint of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L358-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L358-L374

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

theorem GlobalTheory.UnitarySwap.mem_GLint_of_unitary (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L)) {k : GL (Fin n) L} (hk : k ∈ UJ σ (J : Matrix (Fin n) (Fin n) L))
    (hi : ∀ i j, (k : Matrix (Fin n) (Fin n) L) i j ∈ intL L) : k ∈ GLint (Fin n) (intL L) := by sorry
