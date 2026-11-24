-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_hasSum_ideal_of_image
-- name    : GlobalTheory.QuadraticZeta.hasSum_ideal_of_image
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:06.429947+00:00
-- url     : https://prove2.me/theorems/4a203fef-3f3d-4758-b4bb-3da9f58c9dc2
-- title:
--   Quadratic Zeta: has Sum ideal of image
-- statement:
--   The Quadratic Zeta construction uses the has Sum ideal of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L216-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsBasisEmbedding.lean#L216-L246

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

theorem GlobalTheory.QuadraticZeta.hasSum_ideal_of_image (hd : 4 < d) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {ω : ℂ} {τ : ℍ}
    (h : ∀ z, z ∈ σ '' 𝔞.1 ↔ ∃ m n : ℤ, ω * (m * (τ : ℂ) + n) = z) {s : ℝ} (hs : 1 < s)
    (hE : Summable fun p : {p : ℤ × ℤ // p ≠ 0} =>
      τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s)) :
    HasSum (fun I : Ideal (𝓞 K) => open Classical in
      if ((I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal
      then 2 * (Ideal.absNorm I : ℝ) ^ (-s) else 0)
      ((2 / √d) ^ s * ∑' p : {p : ℤ × ℤ // p ≠ 0},
        τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s)) := by sorry
