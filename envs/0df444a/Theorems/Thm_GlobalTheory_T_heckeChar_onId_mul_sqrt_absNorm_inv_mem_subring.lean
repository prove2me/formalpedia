-- Prove2me | Theorems.Thm_GlobalTheory_T_heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring
-- name    : GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:32:32.900331+00:00
-- url     : https://prove2.me/theorems/2324fe4f-fbac-5685-87de-194e3eb18bfb
-- title:
--   T: hecke Char on Id mul sqrt abs Norm inv mem subring
-- statement:
--   The T construction uses the hecke Char on Id mul sqrt abs Norm inv mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)), cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal → (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by sorry
