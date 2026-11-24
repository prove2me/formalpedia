-- Prove2me | Theorems.Thm_GlobalTheory_tsum_ideal_mul_absNorm_cpow_eq_exp_tsum
-- name    : GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:43.593226+00:00
-- url     : https://prove2.me/theorems/fa32939d-cde9-4402-88f6-dabbe7dacb4c
-- title:
--   Global Theory: tsum ideal mul abs Norm cpow eq exp tsum
-- statement:
--   The Global Theory construction uses the tsum ideal mul abs Norm cpow eq exp tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TsumIdealMulAbsNormCpowEqExpTsum.lean#L9-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TsumIdealMulAbsNormCpowEqExpTsum.lean#L9-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum :
    ∀ (K : Type) [Field K] [NumberField K] (X : Ideal (𝓞 K) → ℂ), X ⊥ = 0 → X ⊤ = 1 → (∀ I J, X (I * J) = X I * X J) → (∀ I, ‖X I‖ ≤ 1) → ∀ s : ℂ, 1 < s.re → ∑' I, X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - X P.asIdeal * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by sorry
