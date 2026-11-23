-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_C_mul
-- name    : GlobalTheory.GaussContentLinearForms.span_coeff_C_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:33.78235+00:00
-- url     : https://prove2.me/theorems/ab28c6ea-9471-4dad-a712-0a7cc5753e2e
-- title:
--   Gauss Content Linear Forms: span coeff C mul
-- statement:
--   The Gauss Content Linear Forms construction uses the span coeff C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L9-L20

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

theorem GlobalTheory.GaussContentLinearForms.span_coeff_C_mul (a : V) (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => (C a * f).coeff s) =
      Ideal.span {a} * Ideal.span (Set.range fun s => f.coeff s) := by sorry
