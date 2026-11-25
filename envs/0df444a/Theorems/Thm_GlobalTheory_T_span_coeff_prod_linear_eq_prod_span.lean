-- Prove2me | Theorems.Thm_GlobalTheory_T_span_coeff_prod_linear_eq_prod_span
-- name    : GlobalTheory.T.span_coeff_prod_linear_eq_prod_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:46.831151+00:00
-- url     : https://prove2.me/theorems/eb97a628-42a7-5f6d-b7c5-4eca2c388566
-- title:
--   T: span coeff prod linear eq prod span
-- statement:
--   The T construction uses the span coeff prod linear eq prod span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinearStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinearStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinearStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.span_coeff_prod_linear_eq_prod_span : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (d m : ℕ)
    (c : Fin d → Fin m → V),
    Ideal.span (Set.range fun s => (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by sorry
