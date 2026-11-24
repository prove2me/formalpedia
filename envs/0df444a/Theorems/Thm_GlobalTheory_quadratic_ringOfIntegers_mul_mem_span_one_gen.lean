-- Prove2me | Theorems.Thm_GlobalTheory_quadratic_ringOfIntegers_mul_mem_span_one_gen
-- name    : GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:10.285029+00:00
-- url     : https://prove2.me/theorems/a7500853-3802-4d45-b01e-3318c6b9e679
-- title:
--   Global Theory: quadratic ring Of Integers mul mem span one gen
-- statement:
--   The Global Theory construction uses the quadratic ring Of Integers mul mem span one gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/QuadraticRingOfIntegersMulMemSpanOneGen.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/QuadraticRingOfIntegersMulMemSpanOneGen.lean#L98-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticRingOfIntegersMulMemSpanOneGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
open NumberField IsDedekindDomain

theorem GlobalTheory.quadratic_ringOfIntegers_mul_mem_span_one_gen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → ∃ (θ : 𝓞 E) (D : 𝓞 F), D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) D * y = algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by sorry
