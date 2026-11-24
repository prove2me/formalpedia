-- Prove2me | Theorems.Thm_GlobalTheory_IdemChar_sum_coeff_idemOf_mul
-- name    : GlobalTheory.IdemChar.sum_coeff_idemOf_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:04:49.597322+00:00
-- url     : https://prove2.me/theorems/578f0e61-36b1-4d59-b78b-5a811f02d6fd
-- title:
--   Idem Char: sum coeff idem Of mul
-- statement:
--   The Idem Char construction uses the sum coeff idem Of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumCoeffChiIdemMul.lean#L33-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SumCoeffChiIdemMul.lean#L33-L45

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

theorem GlobalTheory.IdemChar.sum_coeff_idemOf_mul : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ χ ∈ X, ∑ g : G, (idemOf X).coeff g * χ g = χ 1 := by sorry
