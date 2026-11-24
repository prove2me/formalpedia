-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChar_coe_diagHom
-- name    : GlobalTheory.UnitaryChar.coe_diagHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:07.803898+00:00
-- url     : https://prove2.me/theorems/553d2ad2-a47e-483b-9de0-511f669d69d6
-- title:
--   Unitary Char: coe diag Hom
-- statement:
--   The Unitary Char construction uses the coe diag Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean#L99-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitaryChar
variable {n : ℕ}

theorem GlobalTheory.UnitaryChar.coe_diagHom (t : Fin n → Circle) :
    (diagHom n t : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (t i : ℂ) := by sorry
