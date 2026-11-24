-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_form_apply
-- name    : GlobalTheory.UnitarySwap.form_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:46:52.115022+00:00
-- url     : https://prove2.me/theorems/d1fd328b-f09d-4aac-832e-60434f5b4f56
-- title:
--   Unitary Swap: form apply
-- statement:
--   The Unitary Swap construction uses the form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L280-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L280-L281

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
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.UnitarySwap.form_apply (J : Matrix (Fin n) (Fin n) L) (u v : Fin n → L) :
    form σ J u v = (σ ∘ u) ⬝ᵥ (J *ᵥ v) := by sorry
