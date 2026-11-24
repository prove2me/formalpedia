-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_eval_bind_hermSubst
-- name    : GlobalTheory.FibLine.eval_bind_hermSubst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:23:15.871001+00:00
-- url     : https://prove2.me/theorems/64c88425-d32c-4c5c-a154-461b87189d63
-- title:
--   Fib Line: eval bind herm Subst
-- statement:
--   The Fib Line construction uses the eval bind herm Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfEvalHermitian.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfEvalHermitian.lean#L25-L33

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

theorem GlobalTheory.FibLine.eval_bind_hermSubst (P : MvPolynomial (Fin 2 × Fin 2) ℂ) (x : Fin 2 × Fin 2 → ℂ) :
    eval x (bind₁ hermSubst P) =
      eval (entries !![x (0, 0), x (0, 1) + Complex.I * x (1, 0); x (0, 1) - Complex.I * x (1, 0), x (1, 1)]) P := by sorry
