-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_span_coeff_eq_top_iff
-- name    : GlobalTheory.GaussContentLinearForms.span_coeff_eq_top_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:48:23.213307+00:00
-- url     : https://prove2.me/theorems/82ea283a-337b-4378-9a2f-77a29768fd7f
-- title:
--   Gauss Content Linear Forms: span coeff eq top iff
-- statement:
--   The Gauss Content Linear Forms construction uses the span coeff eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L22-L38

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

theorem GlobalTheory.GaussContentLinearForms.span_coeff_eq_top_iff [IsLocalRing V] (f : MvPolynomial σ V) :
    Ideal.span (Set.range fun s => f.coeff s) = ⊤ ↔
      MvPolynomial.map (IsLocalRing.residue V) f ≠ 0 := by sorry
