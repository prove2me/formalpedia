-- Prove2me | Theorems.Thm_GlobalTheory_dedekindZeta_eulerProduct_mul_sub_one_entire
-- name    : GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:40.165088+00:00
-- url     : https://prove2.me/theorems/66a1cede-b685-4849-84f0-299b5933fb1b
-- title:
--   Global Theory: dedekind Zeta euler Product mul sub one entire
-- statement:
--   The Global Theory construction uses the dedekind Zeta euler Product mul sub one entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/DedekindZetaEulerProductMulSubOneEntire.lean#L13-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/DedekindZetaEulerProductMulSubOneEntire.lean#L13-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLSeriesContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealMulAbsNormCpowEqExpTsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_DedekindZetaEulerProductMulSubOneEntire
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
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) *
      Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by sorry
