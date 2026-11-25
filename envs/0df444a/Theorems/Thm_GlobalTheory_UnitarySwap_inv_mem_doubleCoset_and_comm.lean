-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_inv_mem_doubleCoset_and_comm
-- name    : GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:21.278905+00:00
-- url     : https://prove2.me/theorems/6eb9b6e4-e272-41a0-9bd0-ee7652077bf0
-- title:
--   Unitary Swap: inv mem double Coset and comm
-- statement:
--   The Unitary Swap construction uses the inv mem double Coset and comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L461-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L461-L462

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

theorem GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm : (∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (J : GL (Fin n) L), IsUnramInv ϖ σ q → J ∈ GLint (Fin n) (intL L) → (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) → ∀ g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L), ∃ k₁ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), ∃ k₂ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g⁻¹ = k₁ * g * k₂) ∧ HeckeCommU := by sorry
