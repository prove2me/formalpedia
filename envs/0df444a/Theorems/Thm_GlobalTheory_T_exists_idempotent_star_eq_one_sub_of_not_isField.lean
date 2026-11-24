-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_idempotent_star_eq_one_sub_of_not_isField
-- name    : GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:36:05.463287+00:00
-- url     : https://prove2.me/theorems/70bf2cef-8d37-4c40-9830-f8630aa096ba
-- title:
--   T: exists idempotent star eq one sub of not is Field
-- statement:
--   The T construction uses the exists idempotent star eq one sub of not is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIdempotentStarEqOneSubOfNotIsFieldStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIdempotentStarEqOneSubOfNotIsFieldStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIdempotentStarEqOneSubOfNotIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIdempotentStarEqOneSubOfNotIsFieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by sorry
