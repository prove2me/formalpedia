-- Prove2me | Theorems.Thm_GlobalTheory_HeckeIdealValue_inv_mem
-- name    : GlobalTheory.HeckeIdealValue.inv_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:12.467689+00:00
-- url     : https://prove2.me/theorems/e1ac7b66-dd97-407c-94c3-f26063253c53
-- title:
--   Hecke Ideal Value: inv mem
-- statement:
--   The Hecke Ideal Value construction uses the inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L37-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HeckeCharOnIdMulSqrtAbsNormInvMemSubring.lean#L37-L66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HeckeCharOnIdMulSqrtAbsNormInvMemSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeIdealValue
open Formalism.L2.Host
variable {L : Type} [Field L] [NumberField L]

theorem GlobalTheory.HeckeIdealValue.inv_mem (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)) :
    cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal →
      (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) →
    (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by sorry
