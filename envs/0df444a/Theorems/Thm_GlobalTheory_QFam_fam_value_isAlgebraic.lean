-- Prove2me | Theorems.Thm_GlobalTheory_QFam_fam_value_isAlgebraic
-- name    : GlobalTheory.QFam.fam_value_isAlgebraic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:21:49.438665+00:00
-- url     : https://prove2.me/theorems/cc96fc7a-e6b2-43ba-8426-9acc13cf7224
-- title:
--   QFam: fam value is Algebraic
-- statement:
--   The QFam construction uses the fam value is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfIsIntegralAlgebraicNumbers.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfIsIntegralAlgebraicNumbers.lean#L19-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModQPrin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModJTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralModularFamilyValueDivPeriodPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfIsIntegralAlgebraicNumbers
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
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.fam_value_isAlgebraic : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (IsAlgebraic ℚ) N (f i)) → IsAlgebraic ℚ (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsAlgebraic ℚ (f i τ₀ / Ω ^ w) := by sorry
