-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_eval_idFrame_int
-- name    : GlobalTheory.WeylDuality.eval_idFrame_int
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:58.43583+00:00
-- url     : https://prove2.me/theorems/7781517d-e996-411b-a630-365b590d12dc
-- title:
--   Weyl Duality: eval id Frame int
-- statement:
--   The Weyl Duality construction uses the eval id Frame int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L63-L72

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.eval_idFrame_int {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (map (Int.castRingHom ℚ) F) = ((eval (idFrame ℤ r n) F : ℤ) : ℚ) := by sorry
