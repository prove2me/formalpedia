-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_TvKill_exists_double
-- name    : GlobalTheory.UTrans.TvKill.exists_double
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:16.774811+00:00
-- url     : https://prove2.me/theorems/844e9658-43f7-4345-8000-5e1356015d8d
-- title:
--   Tv Kill: exists double
-- statement:
--   The Tv Kill construction uses the exists double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryCharacterKillsUnitaryTransvections.lean#L44-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryCharacterKillsUnitaryTransvections.lean#L44-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryCharacterKillsUnitaryTransvections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.TvKill
open GlobalTheory.UTrans GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.UTrans.TvKill.exists_double [CharZero E] (hG : IsHerm σ G) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : hf σ G x x = 0) : ∃ γ, IsU σ G γ ∧ γ *ᵥ x = (2 : E) • x := by sorry
