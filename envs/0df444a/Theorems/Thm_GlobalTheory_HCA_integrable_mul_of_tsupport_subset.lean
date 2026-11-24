-- Prove2me | Theorems.Thm_GlobalTheory_HCA_integrable_mul_of_tsupport_subset
-- name    : GlobalTheory.HCA.integrable_mul_of_tsupport_subset
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:02.854895+00:00
-- url     : https://prove2.me/theorems/0eb826d1-1687-4113-b4d7-05394da851c4
-- title:
--   HCA: integrable mul of tsupport subset
-- statement:
--   The HCA construction uses the integrable mul of tsupport subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralMulIterPartialDerivEqNegPow.lean#L11-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.integrable_mul_of_tsupport_subset {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by sorry
