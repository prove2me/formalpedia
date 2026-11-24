-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_ne_zero_of_image
-- name    : GlobalTheory.QuadraticZeta.ne_zero_of_image
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:12:14.314715+00:00
-- url     : https://prove2.me/theorems/f2ff464b-b95b-4947-ab80-e8c6cfc63022
-- title:
--   Quadratic Zeta: ne zero of image
-- statement:
--   The Quadratic Zeta construction uses the ne zero of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L196-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L196-L201

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
omit h2 hD

theorem GlobalTheory.QuadraticZeta.ne_zero_of_image {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h0 : 𝔞 ≠ 0) {ω : ℂ} {τ : ℍ}
    (h : ∀ z, z ∈ σ '' 𝔞 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) : ω ≠ 0 := by sorry
