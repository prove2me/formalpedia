-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChar_exists_conj_diagHom
-- name    : GlobalTheory.UnitaryChar.exists_conj_diagHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:27.155064+00:00
-- url     : https://prove2.me/theorems/500e261e-c822-4267-921e-36f59d8db826
-- title:
--   Unitary Char: exists conj diag Hom
-- statement:
--   The Unitary Char construction uses the exists conj diag Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean#L107-L118

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

theorem GlobalTheory.UnitaryChar.exists_conj_diagHom (u : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (V : Matrix.unitaryGroup (Fin n) ℂ) (t : Fin n → Circle), V⁻¹ * u * V = diagHom n t := by sorry
