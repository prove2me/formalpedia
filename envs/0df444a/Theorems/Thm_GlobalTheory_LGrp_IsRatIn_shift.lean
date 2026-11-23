-- Prove2me | Theorems.Thm_GlobalTheory_LGrp_IsRatIn_shift
-- name    : GlobalTheory.LGrp.IsRatIn.shift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:28.664645+00:00
-- url     : https://prove2.me/theorems/d893d982-919b-4511-aade-f97aa56eec3b
-- title:
--   Is Rat In: shift
-- statement:
--   The Is Rat In construction uses the shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/EqOfHasValueAtInfinite.lean#L221-L224

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EqOfHasValueAtInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open GlobalTheory GlobalTheory.LGrp
open Polynomial

theorem GlobalTheory.LGrp.IsRatIn.shift {q : ℕ} (hq : q ≠ 0) {F : ℂ → ℂ} {R : RatFunc ℂ} (h : IsRatIn q F R) (s : ℂ) :
    IsRatIn q (fun z => F (z + s)) (scaleRat (negPowUnit q hq s) R) := by sorry
