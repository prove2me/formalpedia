-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_eq_zero_of_eval_hermitian
-- name    : GlobalTheory.FibLine.eq_zero_of_eval_hermitian
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:23:22.716131+00:00
-- url     : https://prove2.me/theorems/e9908d1b-071c-4252-ac2a-fd97be7f09e8
-- title:
--   Fib Line: eq zero of eval hermitian
-- statement:
--   The Fib Line construction uses the eq zero of eval hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfEvalHermitian.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfEvalHermitian.lean#L35-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfEvalHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine

theorem GlobalTheory.FibLine.eq_zero_of_eval_hermitian (P : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (h : ∀ H : Matrix (Fin 2) (Fin 2) ℂ, H.IsHermitian → MvPolynomial.eval (entries H) P = 0) : P = 0 := by sorry
