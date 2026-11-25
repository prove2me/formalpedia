-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_TvKill_rk_mulVec
-- name    : GlobalTheory.UTrans.TvKill.rk_mulVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:27.327328+00:00
-- url     : https://prove2.me/theorems/19010c0c-19bf-4d72-b5f2-c5c1b67700c6
-- title:
--   Tv Kill: rk mul Vec
-- statement:
--   The Tv Kill construction uses the rk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryCharacterKillsUnitaryTransvections.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryCharacterKillsUnitaryTransvections.lean#L15-L20

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

theorem GlobalTheory.UTrans.TvKill.rk_mulVec (x y v : Fin n → E) : rk σ G x y *ᵥ v = hf σ G v y • x := by sorry
