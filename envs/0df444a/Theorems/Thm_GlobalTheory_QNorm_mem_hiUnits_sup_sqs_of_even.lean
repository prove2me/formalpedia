-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_mem_hiUnits_sup_sqs_of_even
-- name    : GlobalTheory.QNorm.mem_hiUnits_sup_sqs_of_even
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:02:14.153735+00:00
-- url     : https://prove2.me/theorems/e2b0e6e6-30ba-4f4c-b896-34bba6129230
-- title:
--   QNorm: mem hi Units sup sqs of even
-- statement:
--   The QNorm construction uses the mem hi Units sup sqs of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSquaresLeTwoMulUnitsSquares.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexSquaresLeTwoMulUnitsSquares.lean#L9-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSquaresLeTwoMulUnitsSquares
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.mem_hiUnits_sup_sqs_of_even {K : Type} [Field K] (w : Valuation K ℤᵐ⁰) (p : Kˣ)
    (hp : w (p : K) = WithZero.exp (-1)) (x : Kˣ) (m : ℤ)
    (hx : w (x : K) = WithZero.exp (2 * m)) :
    x ∈ hiUnits w 0 ⊔ sqs (⊤ : Subgroup Kˣ) := by sorry
