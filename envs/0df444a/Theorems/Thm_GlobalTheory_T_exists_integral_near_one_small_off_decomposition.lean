-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_integral_near_one_small_off_decomposition
-- name    : GlobalTheory.T.exists_integral_near_one_small_off_decomposition
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:33:42.157737+00:00
-- url     : https://prove2.me/theorems/3629aa45-b072-4c46-9a1d-242e56d031a6
-- title:
--   T: exists integral near one small off decomposition
-- statement:
--   The T construction uses the exists integral near one small off decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrtApproxIntegralStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CrtApproxIntegralStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_integral_near_one_small_off_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A : ValuationSubring Ω) (c : ℕ), c ≠ 0 → ∃ t ∈ K, IsIntegral ℤ t ∧ A.valuation (t - 1) ≤ A.valuation (c : Ω) ∧ ∀ σ : G E Ω, (∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)) → A.valuation (σ t) ≤ A.valuation (c : Ω) := by sorry
