-- Prove2me | Theorems.Thm_GlobalTheory_GaussContentLinearForms_exists_primitive_part
-- name    : GlobalTheory.GaussContentLinearForms.exists_primitive_part
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:02.499798+00:00
-- url     : https://prove2.me/theorems/6a80e457-b377-4453-bd47-1738db281d14
-- title:
--   Gauss Content Linear Forms: exists primitive part
-- statement:
--   The Gauss Content Linear Forms construction uses the exists primitive part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L46-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanCoeffProdLinear.lean#L46-L66

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

theorem GlobalTheory.GaussContentLinearForms.exists_primitive_part [IsDomain V] [IsDiscreteValuationRing V] (f : MvPolynomial σ V) :
    ∃ (a : V) (g : MvPolynomial σ V), f = C a * g ∧
      Ideal.span (Set.range fun s => g.coeff s) = ⊤ := by sorry
