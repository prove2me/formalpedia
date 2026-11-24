-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChar_exists_conj_perm
-- name    : GlobalTheory.UnitaryChar.exists_conj_perm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:39:19.609844+00:00
-- url     : https://prove2.me/theorems/f8cb34ec-0d57-47f4-a4dc-e2fd839dd978
-- title:
--   Unitary Char: exists conj perm
-- statement:
--   The Unitary Char construction uses the exists conj perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean#L120-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean#L120-L131

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

theorem GlobalTheory.UnitaryChar.exists_conj_perm (σ : Equiv.Perm (Fin n)) (t : Fin n → Circle) :
    ∃ P : Matrix.unitaryGroup (Fin n) ℂ, P * diagHom n t = diagHom n (t ∘ σ) * P := by sorry
