-- Prove2me | Theorems.Thm_GlobalTheory_UpqChar_char_unitary
-- name    : GlobalTheory.UpqChar.char_unitary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:08:36.877901+00:00
-- url     : https://prove2.me/theorems/45640ba1-3b70-43df-87fb-54c9eade8d5c
-- title:
--   Upq Char: char unitary
-- statement:
--   The Upq Char construction uses the char unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryPQContinuousCharacterEqDetPowProd.lean#L33-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryPQContinuousCharacterEqDetPowProd.lean#L33-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryPQContinuousCharacterEqDetPowProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UpqChar

theorem GlobalTheory.UpqChar.char_unitary {p : ℕ} (f : Matrix.unitaryGroup (Fin p) ℂ → ℂ)
    (hmul : ∀ a b, f (a * b) = f a * f b) (hn : ∀ a, ‖f a‖ = 1) (hc : Continuous f) :
    ∃ x : ℤ, ∀ a, f a = (Matrix.det (a : Matrix (Fin p) (Fin p) ℂ)) ^ x := by sorry
