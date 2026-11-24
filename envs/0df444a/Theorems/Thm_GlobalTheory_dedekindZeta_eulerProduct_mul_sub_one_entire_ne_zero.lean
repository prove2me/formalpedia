-- Prove2me | Theorems.Thm_GlobalTheory_dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero
-- name    : GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:32.845668+00:00
-- url     : https://prove2.me/theorems/992e4b88-7e54-4234-a1e7-f89e196b33a4
-- title:
--   Global Theory: dedekind Zeta euler Product mul sub one entire ne zero
-- statement:
--   The Global Theory construction uses the dedekind Zeta euler Product mul sub one entire ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DedekindZetaEulerProductMulSubOneEntireNeZero.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DedekindZetaEulerProductMulSubOneEntireNeZero.lean#L40-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DedekindZetaEulerProductMulSubOneEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DedekindZetaEulerProductMulSubOneEntireNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero :
    ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by sorry
