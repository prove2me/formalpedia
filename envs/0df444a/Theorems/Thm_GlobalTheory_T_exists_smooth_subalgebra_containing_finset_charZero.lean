-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_smooth_subalgebra_containing_finset_charZero
-- name    : GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:06.470003+00:00
-- url     : https://prove2.me/theorems/b2e8334e-0643-5715-9109-514544dde7ea
-- title:
--   T: exists smooth subalgebra containing finset char Zero
-- statement:
--   The T construction uses the exists smooth subalgebra containing finset char Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSubalgebraContainingFinsetCharZeroStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSubalgebraContainingFinsetCharZeroStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSubalgebraContainingFinsetCharZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSubalgebraContainingFinsetCharZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by sorry
