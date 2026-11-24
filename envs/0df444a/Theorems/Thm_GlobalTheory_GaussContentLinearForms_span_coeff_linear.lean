-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_linear
-- name    : GlobalTheory.GaussContentLinearForms.span_coeff_linear
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:38.696664+00:00
-- url     : https://prove2.me/theorems/1d0b61ce-7802-4660-82bf-61494f2f3432
-- title:
--   Gauss Content Linear Forms: span coeff linear
-- statement:
--   The Gauss Content Linear Forms construction uses the span coeff linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L91-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L91-L110

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

theorem GlobalTheory.GaussContentLinearForms.span_coeff_linear {m : ℕ} (c : Fin m → V) :
    Ideal.span (Set.range fun s => (∑ i, C (c i) * X i : MvPolynomial (Fin m) V).coeff s) =
      Ideal.span (Set.range c) := by sorry
