-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LamRay_sum_lamIdeal_le
-- name    : GlobalTheory.Hk.LamRay.sum_lamIdeal_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:35:16.520473+00:00
-- url     : https://prove2.me/theorems/e78674cc-aadd-469b-a2b5-a4c6c56f5aa6
-- title:
--   Lam Ray: sum lam Ideal le
-- statement:
--   The Lam Ray construction uses the sum lam Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L38-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L38-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Hk.LamRay.sum_lamIdeal_le (hK : Module.finrank ℚ K = 2) (n : ℕ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S, Ideal.absNorm I = n) : ∑ I ∈ S, lamIdeal I ≤ 2 * Λ n := by sorry
