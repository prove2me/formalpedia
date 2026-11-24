-- Prove2me | Theorems.Thm_GlobalTheory_Hk_RayConv_sum_lamIdeal
-- name    : GlobalTheory.Hk.RayConv.sum_lamIdeal
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:34:57.928891+00:00
-- url     : https://prove2.me/theorems/55e1ef82-98cb-42da-87b0-48f879618eba
-- title:
--   Ray Conv: sum lam Ideal
-- statement:
--   The Ray Conv construction uses the sum lam Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteIdealsIn.lean#L20-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FiniteIdealsIn.lean#L20-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayConv
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Hk.RayConv.sum_lamIdeal (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by sorry
