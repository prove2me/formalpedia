-- Prove2me | Theorems.Thm_GlobalTheory_eq_I_mul_sqrt_or_of_sq_eq_neg
-- name    : GlobalTheory.eq_I_mul_sqrt_or_of_sq_eq_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:13.562314+00:00
-- url     : https://prove2.me/theorems/8f90d496-414b-4882-8e7b-b870305d540b
-- title:
--   Global Theory: eq I mul sqrt or of sq eq neg
-- statement:
--   The Global Theory construction uses the eq I mul sqrt or of sq eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RingOfIntegersSqrtNegThreeModFour.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RingOfIntegersSqrtNegThreeModFour.lean#L158-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory
open QuadraticZeta

theorem GlobalTheory.eq_I_mul_sqrt_or_of_sq_eq_neg {d : ℕ} {z : ℂ} (hz : z ^ 2 = -d) :
    z = Complex.I * √d ∨ z = -(Complex.I * √d) := by sorry
