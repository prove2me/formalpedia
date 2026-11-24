-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_dualWeyl_int_fg
-- name    : GlobalTheory.WeylDuality.dualWeyl_int_fg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:56.954628+00:00
-- url     : https://prove2.me/theorems/bcb1e852-8de7-4d2b-9459-b0b773803e7f
-- title:
--   Weyl Duality: dual Weyl int fg
-- statement:
--   The Weyl Duality construction uses the dual Weyl int fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L248-L253

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

theorem GlobalTheory.WeylDuality.dualWeyl_int_fg (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by sorry
