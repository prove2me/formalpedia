-- Prove2me | Theorems.Thm_GlobalTheory_T_valuation_le_one_of_sq_sub_self_integral_basis
-- name    : GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:01:28.072054+00:00
-- url     : https://prove2.me/theorems/26881f48-0494-4f28-b513-969e0d7d5661
-- title:
--   T: valuation le one of sq sub self integral basis
-- statement:
--   The T construction uses the valuation le one of sq sub self integral basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationLeOneOfSqSubSelfIntegralBasisStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationLeOneOfSqSubSelfIntegralBasisStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasis
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationLeOneOfSqSubSelfIntegralBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] {ι : Type} [Fintype ι] (b : Module.Basis ι E E'), (∀ i, IsIntegral ℤ (b i)) → ∀ (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E')), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal → ∀ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) → w''.valuation E' ε ≤ 1 := by sorry
