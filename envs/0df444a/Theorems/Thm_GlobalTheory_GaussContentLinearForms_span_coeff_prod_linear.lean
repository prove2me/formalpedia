-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_prod_linear
-- name    : GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:48.33752+00:00
-- url     : https://prove2.me/theorems/ee0fe12d-d93e-4584-9295-7d94ba17d4d4
-- title:
--   Gauss Content Linear Forms: span coeff prod linear
-- statement:
--   The Gauss Content Linear Forms construction uses the span coeff prod linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L112-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanCoeffProdLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.GaussContentLinearForms
variable {V : Type} [CommRing V] {σ : Type}

theorem GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (d m : ℕ) (c : Fin d → Fin m → V) :
    Ideal.span (Set.range fun s =>
        (∏ j, ∑ i, C (c j i) * X i : MvPolynomial (Fin m) V).coeff s) =
      ∏ j, Ideal.span (Set.range (c j)) := by sorry
