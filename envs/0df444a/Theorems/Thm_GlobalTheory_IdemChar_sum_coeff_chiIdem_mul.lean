-- Prove2me | Theorems.Thm_GlobalTheory_IdemChar_sum_coeff_chiIdem_mul
-- name    : GlobalTheory.IdemChar.sum_coeff_chiIdem_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:37.228562+00:00
-- url     : https://prove2.me/theorems/f1eb4389-dabb-434b-bcc2-27713a90df31
-- title:
--   Idem Char: sum coeff chi Idem mul
-- statement:
--   The Idem Char construction uses the sum coeff chi Idem mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumCoeffChiIdemMul.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumCoeffChiIdemMul.lean#L11-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumCoeffChiIdemMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.DIV
open GlobalTheory GlobalTheory.IdemChar
open Classical

theorem GlobalTheory.IdemChar.sum_coeff_chiIdem_mul {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
    {φ χ : G → K} (hφ : IsAbsIrrChar φ) (hχ : IsAbsIrrChar χ) :
    ∑ g : G, (chiIdem φ).coeff g * χ g = if φ = χ then χ 1 else 0 := by sorry
