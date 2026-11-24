-- Prove2me | Theorems.Thm_GlobalTheory_T_isAdicComplete_of_fg_of_natCast_mem_of_integers
-- name    : GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:58.788399+00:00
-- url     : https://prove2.me/theorems/5a325de7-a6d7-45c3-930b-beefe46c8d8d
-- title:
--   T: is Adic Complete of fg of nat Cast mem of integers
-- statement:
--   The T construction uses the is Adic Complete of fg of nat Cast mem of integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMemStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMemStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMemStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isAdicComplete_of_fg_of_natCast_mem_of_integers : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → IsAdicComplete J O := by sorry
