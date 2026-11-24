-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_selfDual_image
-- name    : GlobalTheory.UnitarySwap.selfDual_image
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:46:08.593296+00:00
-- url     : https://prove2.me/theorems/f3888222-09a5-4274-b2aa-3ab7c4bd7c7c
-- title:
--   Unitary Swap: self Dual image
-- statement:
--   The Unitary Swap construction uses the self Dual image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L342-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L342-L356

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

theorem GlobalTheory.UnitarySwap.selfDual_image {J : Matrix (Fin n) (Fin n) L} {Λ : Set (Fin n → L)}
    (h : SelfDual (form σ J) ⊤ Λ) {g : GL (Fin n) L} (hg : g ∈ UJ σ J) :
    SelfDual (form σ J) ⊤ {v | (g : Matrix (Fin n) (Fin n) L) *ᵥ v ∈ Λ} := by sorry
