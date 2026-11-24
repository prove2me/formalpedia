-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_mul
-- name    : GlobalTheory.GaussContentLinearForms.span_coeff_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:29.997032+00:00
-- url     : https://prove2.me/theorems/76df0550-b23b-4d1d-a6ef-2861c56ef2d8
-- title:
--   Gauss Content Linear Forms: span coeff mul
-- statement:
--   The Gauss Content Linear Forms construction uses the span coeff mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L68-L80

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

theorem GlobalTheory.GaussContentLinearForms.span_coeff_mul [IsDomain V] [IsDiscreteValuationRing V] (f g : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (f * g).coeff s) =
      Ideal.span (Set.range fun s => f.coeff s) * Ideal.span (Set.range fun s => g.coeff s) := by sorry
