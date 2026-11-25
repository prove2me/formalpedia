-- Prove2me | Theorems.Thm_NormOnePowProof_conj_span
-- name    : NormOnePowProof.conj_span
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:38.680052+00:00
-- url     : https://prove2.me/theorems/7c48b262-4c3b-4c79-b0ee-e817fd404d62
-- title:
--   Norm One Pow Proof: conj span
-- statement:
--   The Norm One Pow Proof construction uses the conj span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOnePowerPrincipal/PowPrincipal.lean#L60-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormOnePowerPrincipal/PowPrincipal.lean#L60-L76

import Definitions.Def_Formalism_PeriodIntegrals_NormOnePow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOnePowerPrincipal_PowPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors
open NormOnePowProof
variable {E : Type} [Field E] [NumberField E]

theorem NormOnePowProof.conj_span (c : E →+* E) (hc : ∀ x, c (c x) = x) {B : Submodule (𝓞 E) E} (a : E)
    (hB : ∀ x, x ∈ B ↔ c x ∈ Submodule.span (𝓞 E) {a}) :
    B = Submodule.span (𝓞 E) {c a} := by sorry
