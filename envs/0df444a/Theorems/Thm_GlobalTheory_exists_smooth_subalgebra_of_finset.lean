-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_subalgebra_of_finset
-- name    : GlobalTheory.exists_smooth_subalgebra_of_finset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:32.086851+00:00
-- url     : https://prove2.me/theorems/d6e20b62-ac43-4ac9-b742-cc11bdc4b168
-- title:
--   Global Theory: exists smooth subalgebra of finset
-- statement:
--   The Global Theory construction uses the exists smooth subalgebra of finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSubalgebraContainingFinsetCharZero.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmoothSubalgebraContainingFinsetCharZero.lean#L8-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSubalgebraContainingFinsetCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_smooth_subalgebra_of_finset : ∀ (F K : Type) [Field F] [CharZero F] [Field K]
    [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧
      Algebra.Smooth F R := by sorry
