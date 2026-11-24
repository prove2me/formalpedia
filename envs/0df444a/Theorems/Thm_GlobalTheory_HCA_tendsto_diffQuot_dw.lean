-- Prove2me | Theorems.Thm_GlobalTheory_HCA_tendsto_diffQuot_dw
-- name    : GlobalTheory.HCA.tendsto_diffQuot_dw
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:59:52.361487+00:00
-- url     : https://prove2.me/theorems/c002e3cd-39c2-430f-8f74-cce2533ad93f
-- title:
--   HCA: tendsto diff Quot dw
-- statement:
--   The HCA construction uses the tendsto diff Quot dw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousFunctionalIterPartialDeriv.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsContinuousFunctionalIterPartialDeriv.lean#L11-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.tendsto_diffQuot_dw {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (f : E d → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (w : List (Fin d)) (j : Fin d) {x : E d} (hx : x ∈ U) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (dw w f (x + (1 / ((n : ℝ) + 1)) • ev j) - dw w f x))
      atTop (𝓝 (dw (j :: w) f x)) := by sorry
