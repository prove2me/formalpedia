-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_absNorm_eq_of_image
-- name    : GlobalTheory.QuadraticZeta.absNorm_eq_of_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:21.144593+00:00
-- url     : https://prove2.me/theorems/671332b4-ff57-48e2-a81a-7a0baa6ca34d
-- title:
--   Quadratic Zeta: abs Norm eq of image
-- statement:
--   The Quadratic Zeta construction uses the abs Norm eq of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L203-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L203-L214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD

theorem GlobalTheory.QuadraticZeta.absNorm_eq_of_image {𝔞 : FractionalIdeal (𝓞 K)⁰ K} {ω : ℂ} {τ : ℍ} (hω : ω ≠ 0)
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) :
    (absNorm 𝔞 : ℝ) = 2 * ‖ω‖ ^ 2 * τ.im / √d := by sorry
