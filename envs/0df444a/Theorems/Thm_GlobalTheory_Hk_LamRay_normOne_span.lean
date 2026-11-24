-- Prove2me | Theorems.Thm_GlobalTheory_Hk_LamRay_normOne_span
-- name    : GlobalTheory.Hk.LamRay.normOne_span
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:22:05.289309+00:00
-- url     : https://prove2.me/theorems/32d8bb3f-b6df-41a6-94e2-6d3179d78475
-- title:
--   Lam Ray: norm One span
-- statement:
--   The Lam Ray construction uses the norm One span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L113-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumLamIdealLe.lean#L113-L130

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

theorem GlobalTheory.Hk.LamRay.normOne_span {d M : ℕ} {ω : 𝓞 K} (hgen : ∀ z : 𝓞 K, ∃ a b : ℤ, z = a + b * ω)
    (hnorm : ∀ a b : ℤ,
      Algebra.norm ℤ ((a : 𝓞 K) + b * ω) * 4 = (2 * a + b) ^ 2 + d * b ^ 2)
    {π : 𝓞 K} (hπ : π - 1 ∈ Ideal.span {(M : 𝓞 K)}) :
    GlobalTheory.Mem.An.NormOne d M (Ideal.absNorm (Ideal.span {π})) := by sorry
