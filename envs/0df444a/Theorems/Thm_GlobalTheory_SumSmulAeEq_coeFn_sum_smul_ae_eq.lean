-- Prove2me | Theorems.Thm_GlobalTheory_SumSmulAeEq_coeFn_sum_smul_ae_eq
-- name    : GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:06.228972+00:00
-- url     : https://prove2.me/theorems/0a1660a3-5e28-4a37-b45c-844129842e98
-- title:
--   Sum Smul Ae Eq: coe Fn sum smul ae eq
-- statement:
--   The Sum Smul Ae Eq construction uses the coe Fn sum smul ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CoeFnSumSmulAeEq.lean#L7-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CoeFnSumSmulAeEq.lean#L7-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CoeFnSumSmulAeEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SumSmulAeEq
open MeasureTheory

theorem GlobalTheory.SumSmulAeEq.coeFn_sum_smul_ae_eq {X ι : Type} [MeasurableSpace X] (μ : Measure X) (s : Finset ι)
    (c : ι → ℂ) (y : ι → Lp ℂ (2 : ENNReal) μ) (F : ι → X → ℂ)
    (h : ∀ i, (y i : X → ℂ) =ᵐ[μ] F i) :
    ((∑ i ∈ s, c i • y i : Lp ℂ (2 : ENNReal) μ) : X → ℂ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * F i x := by sorry
