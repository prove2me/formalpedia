-- Prove2me | Theorems.Thm_GlobalTheory_Nef_isRat_iff_exists_ratFunc
-- name    : GlobalTheory.Nef.isRat_iff_exists_ratFunc
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:45.110543+00:00
-- url     : https://prove2.me/theorems/a938717b-ec80-5c43-b420-fe73d6293a5f
-- title:
--   Nef: is Rat iff exists rat Func
-- statement:
--   The Nef construction uses the is Rat iff exists rat Func property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatIffExistsRatFunc.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatIffExistsRatFunc.lean#L9-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatIffExistsRatFunc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.isRat_iff_exists_ratFunc : ∀ (F : Type) [Field F] (φ : PowerSeries F), IsRat φ ↔
    ∃ ρ : RatFunc F, algebraMap (RatFunc F) (LaurentSeries F) ρ = algebraMap (PowerSeries F) (LaurentSeries F) φ := by sorry
