-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_modularFamily_value_div_period_pow
-- name    : GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:12:35.011557+00:00
-- url     : https://prove2.me/theorems/4aa13c7d-91e1-4d4b-bc30-00cf8edece03
-- title:
--   T: is Integral modular Family value div period pow
-- statement:
--   The T construction uses the is Integral modular Family value div period pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralModularFamilyValueDivPeriodPowStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralModularFamilyValueDivPeriodPowStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → IsIntegral R (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsIntegral R (f i τ₀ / Ω ^ w) := by sorry
