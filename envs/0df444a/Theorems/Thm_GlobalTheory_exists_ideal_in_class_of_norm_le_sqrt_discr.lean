-- Prove2me | Theorems.Thm_GlobalTheory_exists_ideal_in_class_of_norm_le_sqrt_discr
-- name    : GlobalTheory.exists_ideal_in_class_of_norm_le_sqrt_discr
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:30.848494+00:00
-- url     : https://prove2.me/theorems/31154105-65af-4d6e-9bc1-bacd7bd4659f
-- title:
--   Global Theory: exists ideal in class of norm le sqrt discr
-- statement:
--   The Global Theory construction uses the exists ideal in class of norm le sqrt discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L251-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIdealInClassOfNormLeSqrtDiscr.lean#L251-L257

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

theorem GlobalTheory.exists_ideal_in_class_of_norm_le_sqrt_discr (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ √|(discr K : ℝ)| := by sorry
