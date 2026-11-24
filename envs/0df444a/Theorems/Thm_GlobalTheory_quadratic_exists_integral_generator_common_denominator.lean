-- Prove2me | Theorems.Thm_GlobalTheory_quadratic_exists_integral_generator_common_denominator
-- name    : GlobalTheory.quadratic_exists_integral_generator_common_denominator
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:01.878492+00:00
-- url     : https://prove2.me/theorems/f185304a-9c40-42dd-8477-15a76f2baa28
-- title:
--   Global Theory: quadratic exists integral generator common denominator
-- statement:
--   The Global Theory construction uses the quadratic exists integral generator common denominator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/QuadraticExistsIntegralGeneratorCommonDenominato.lean#L99-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/QuadraticExistsIntegralGeneratorCommonDenominato.lean#L99-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticRingOfIntegersMulMemSpanOneGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_QuadraticExistsIntegralGeneratorCommonDenominato
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory
open NumberField

theorem GlobalTheory.quadratic_exists_integral_generator_common_denominator :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [Algebra.IsQuadraticExtension F E], ∃ θ : 𝓞 E, (θ : E) ∉ Set.range (algebraMap F E) ∧
      ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ y : 𝓞 E, ∃ u v : 𝓞 F,
        algebraMap (𝓞 F) (𝓞 E) D * y =
          algebraMap (𝓞 F) (𝓞 E) u + algebraMap (𝓞 F) (𝓞 E) v * θ := by sorry
