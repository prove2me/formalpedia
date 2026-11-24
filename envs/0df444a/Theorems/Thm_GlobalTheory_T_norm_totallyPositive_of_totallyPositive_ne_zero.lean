-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_totallyPositive_of_totallyPositive_ne_zero
-- name    : GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:52.826849+00:00
-- url     : https://prove2.me/theorems/1e6b91d1-3e0d-467e-a896-3a5f066914d1
-- title:
--   T: norm totally Positive of totally Positive ne zero
-- statement:
--   The T construction uses the norm totally Positive of totally Positive ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormTotallyPositiveOfTotallyPositiveNeZeroStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormTotallyPositiveOfTotallyPositiveNeZeroStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormTotallyPositiveOfTotallyPositiveNeZero
import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocUnitApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormTotallyPositiveOfTotallyPositiveNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (a : E'), a ≠ 0 → (∀ φ : E' →+* ℝ, 0 < φ a) → ∀ φ : E →+* ℝ, 0 < φ (Algebra.norm E a) := by sorry
