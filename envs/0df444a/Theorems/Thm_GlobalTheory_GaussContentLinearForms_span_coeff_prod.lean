-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_prod
-- name    : GlobalTheory.GaussContentLinearForms.span_coeff_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:40.180241+00:00
-- url     : https://prove2.me/theorems/a176294f-c55b-434c-bd77-860a46148445
-- title:
--   Gauss Content Linear Forms: span coeff prod
-- statement:
--   The Gauss Content Linear Forms construction uses the span coeff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L82-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L82-L89

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

theorem GlobalTheory.GaussContentLinearForms.span_coeff_prod [IsDomain V] [IsDiscreteValuationRing V] {ι : Type} (t : Finset ι)
    (f : ι → MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (∏ j ∈ t, f j).coeff s) =
      ∏ j ∈ t, Ideal.span (Set.range fun s => (f j).coeff s) := by sorry
