-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySwap_inv_mem_doubleCoset
-- name    : GlobalTheory.UnitarySwap.inv_mem_doubleCoset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:06.402924+00:00
-- url     : https://prove2.me/theorems/02615075-925e-41a4-8d5b-5ee416b68e4b
-- title:
--   Unitary Swap: inv mem double Coset
-- statement:
--   The Unitary Swap construction uses the inv mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L386-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/InvMemDoubleCosetAndComm.lean#L386-L428

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

theorem GlobalTheory.UnitarySwap.inv_mem_doubleCoset {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {J : GL (Fin n) L}
    (hJ : J ∈ GLint (Fin n) (intL L))
    (hh : ∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i)
    {g : GL (Fin n) L} (hg : g ∈ UJ σ (J : Matrix (Fin n) (Fin n) L)) :
    ∃ k₁ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (J : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g⁻¹ = k₁ * g * k₂ := by sorry
