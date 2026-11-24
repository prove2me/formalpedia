-- Prove2me | Theorems.Thm_GlobalTheory_T_span_pow_generator_eq_top_of_charpoly_separable
-- name    : GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:26.236287+00:00
-- url     : https://prove2.me/theorems/195e7685-364c-4126-ab9e-d01ef7bde280
-- title:
--   T: span pow generator eq top of charpoly separable
-- statement:
--   The T construction uses the span pow generator eq top of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanPowGeneratorEqTopOfCharpolySeparableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanPowGeneratorEqTopOfCharpolySeparableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanPowGeneratorEqTopOfCharpolySeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanPowGeneratorEqTopOfCharpolySeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by sorry
