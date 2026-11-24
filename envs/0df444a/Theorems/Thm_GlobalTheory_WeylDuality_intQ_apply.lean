-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_intQ_apply
-- name    : GlobalTheory.WeylDuality.intQ_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:46.550365+00:00
-- url     : https://prove2.me/theorems/a1f21ff2-abbe-4a0a-9587-75e62274795d
-- title:
--   Weyl Duality: int Q apply
-- statement:
--   The Weyl Duality construction uses the int Q apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L10-L11

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

theorem GlobalTheory.WeylDuality.intQ_apply {r n : ℕ} (F : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n F = map (Int.castRingHom ℚ) F := by sorry
