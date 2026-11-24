-- Prove2me | Theorems.Thm_GlobalTheory_isAdicComplete_of_fg_of_natCast_mem
-- name    : GlobalTheory.isAdicComplete_of_fg_of_natCast_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:15.614118+00:00
-- url     : https://prove2.me/theorems/e6cd0011-1b93-49f9-9bff-f3b4ade53096
-- title:
--   Global Theory: is Adic Complete of fg of nat Cast mem
-- statement:
--   The Global Theory construction uses the is Adic Complete of fg of nat Cast mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMem.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsAdicCompleteOfFgOfNatCastMem.lean#L62-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isAdicComplete_of_fg_of_natCast_mem : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → IsAdicComplete J O := by sorry
