-- Prove2me | Theorems.Thm_GlobalTheory_ncard_ideal_absNorm_eq_le
-- name    : GlobalTheory.ncard_ideal_absNorm_eq_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:12:03.348689+00:00
-- url     : https://prove2.me/theorems/4ae026ec-1307-493d-a0f1-a638010f9030
-- title:
--   Global Theory: ncard ideal abs Norm eq le
-- statement:
--   The Global Theory construction uses the ncard ideal abs Norm eq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L128-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L128-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]

theorem GlobalTheory.ncard_ideal_absNorm_eq_le {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard
      ≤ (ζ ^ finrank ℚ K : ArithmeticFunction ℕ) n := by sorry
